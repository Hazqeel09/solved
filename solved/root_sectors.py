"""Constructive square-root reduction in the three- and seven-nonsquare sectors.

This is not a root extractor for arbitrary AM chains. Unsupported chains
are rejected explicitly. The all-length coverage argument is recorded in
results/root-closure-sectors/PROOF.md; every returned program is replay-checked.
"""

from dataclasses import dataclass
from functools import lru_cache
from math import isqrt

from .chains import Chain, level
from .seven_steps import catalogue as seven_catalogue
from .square_controls import encode


@dataclass(frozen=True)
class RootReduction:
    root: int
    chain: Chain
    source_length: int
    rule: str

    @property
    def saved_instructions(self):
        return self.source_length - len(self.chain.recipes)


class _Builder:
    def __init__(self, chain):
        self.values = list(chain.values)
        self.recipes = list(chain.recipes)
        self.positions = {value: i for i, value in enumerate(self.values)}

    def append(self, op, left, right):
        if left not in self.positions or right not in self.positions:
            raise ArithmeticError("root construction requests an unavailable operand")
        value = left + right if op == "+" else left * right
        if value <= self.values[-1]:
            raise ArithmeticError("root construction is not strictly increasing")
        a, b = sorted((self.positions[left], self.positions[right]))
        self.recipes.append((op, a, b))
        self.positions[value] = len(self.values)
        self.values.append(value)
        return value

    def finish(self):
        return Chain(tuple(self.values), tuple(self.recipes))


def _prefix(chain, index):
    return Chain(chain.values[: index + 1], chain.recipes[:index])


def _power_of_two(value):
    return value > 0 and value & (value - 1) == 0


def _small_root(root):
    builder = _Builder(Chain((1, 2), (("+", 0, 0),)))
    builder.append("+", 1, 2)
    if root == 6:
        builder.append("*", 2, 3)
    elif root != 3:
        raise ArithmeticError("unknown exceptional root")
    return builder.finish()


def _from_values(values):
    """Compile an existing numerical witness, choosing one valid recipe per write."""
    recipes = []
    for i, value in enumerate(values[1:], 1):
        rule = next(
            (
                (op, a, b)
                for a in range(i)
                for b in range(a, i)
                for op, result in (("+", values[a] + values[b]), ("*", values[a] * values[b]))
                if result == value
            ),
            None,
        )
        if rule is None:
            raise ArithmeticError("a catalogue witness has no legal recipe")
        recipes.append(rule)
    return Chain(tuple(values), tuple(recipes))


@lru_cache(maxsize=1)
def _seven_models():
    return tuple(
        (row["base"], _from_values(row["witness"])) for row in seven_catalogue()["squaring_rays"]
    )


def _seven_root(target):
    models = dict(_seven_models())
    base, outer = target, 0
    while base not in models:
        root = isqrt(base)
        if root * root != base or root < 2:
            raise ArithmeticError("the seven-event chain is outside the classified rays")
        base, outer = root, outer + 1
    if outer:
        builder = _Builder(models[base])
        for _ in range(outer - 1):
            head = builder.values[-1]
            builder.append("*", head, head)
        return builder.finish(), "seven_ray"
    exceptional = {
        11019960576: (1, 2, 3, 6, 18, 324, 104976),
        17179869184: (1, 2, 4, 16, 256, 65536, 131072),
        18446744073709551616: (1, 2, 4, 16, 256, 65536, 4294967296),
    }
    if base not in exceptional:
        raise ArithmeticError("unclassified square base in the seven-event catalogue")
    return _from_values(exceptional[base]), "seven_square_base"


def reduce_square(chain):
    """Return a root program saving at least one write in the declared sector."""
    if not isinstance(chain, Chain):
        raise ValueError("an AM chain is required")
    chain = Chain(tuple(chain.values), tuple(tuple(row) for row in chain.recipes))
    encode(chain)  # Existing full structural and exact-arithmetic validation.
    values, recipes = chain.values, chain.recipes
    source_length = len(recipes)
    if source_length - level(values[-1]) != 2:
        raise ValueError("exactly two small steps are required")
    events = tuple(i for i in range(1, len(values)) if values[i] != values[i - 1] ** 2)
    if len(events) not in (3, 7):
        raise ValueError("exactly three or seven canonical nonsquare writes are required")
    root = isqrt(values[-1])
    if root * root != values[-1]:
        raise ValueError("the endpoint must be an integer square")

    def result(output, rule):
        encode(output)
        if output.values[-1] != root or len(output.recipes) >= source_length:
            raise ArithmeticError("root-reduction certificate failed")
        if len(output.recipes) - level(root) > 2:
            raise ArithmeticError("root witness exceeds the defect budget")
        return RootReduction(root, output, source_length, rule)

    if values[-1] == values[-2] ** 2:
        return result(_prefix(chain, source_length - 1), "trailing_square")
    if len(events) == 7:
        output, rule = _seven_root(values[-1])
        return result(output, rule)

    first = events[1]
    A, B = values[first - 1], values[first]
    gap = events[2] - first - 1
    op, a, b = recipes[-1]
    left, right = values[a], values[b]

    def doubled_tower_root():
        rA = isqrt(A)
        if rA * rA != A or values[-1] != 4 * A:
            raise ArithmeticError("invalid doubled-tower square")
        builder = _Builder(_prefix(chain, first - 2))
        builder.append("+", rA, rA)
        return builder.finish()

    def rooted_first_product():
        rA, rB = isqrt(A), isqrt(B)
        if rA * rA != A or rB * rB != B or B % A:
            raise ArithmeticError("the first small value is not a square tower product")
        factor = B // A
        rf = isqrt(factor)
        if rf * rf != factor or factor not in values[:first]:
            raise ArithmeticError("the first product's factor is not a square tower entry")
        builder = _Builder(_prefix(chain, first - 2))
        builder.append("*", rA, rf)
        return builder, rB

    if op == "+":
        if gap:
            raise ArithmeticError("a sum after a positive square run cannot be square")
        if root in (3, 6):
            return result(_small_root(root), "exceptional_sum")
        return result(doubled_tower_root(), "doubled_tower_sum")

    if gap:
        head = values[-2]
        if head not in (left, right):
            raise ArithmeticError("a post-run nonsquare product must read its head")
        other = right if left == head else left
        rhead, rother = isqrt(head), isqrt(other)
        if rhead * rhead != head or rother * rother != other:
            raise ArithmeticError("square product with a square head has a nonsquare cofactor")
        shortened = _prefix(chain, source_length - 2)
        if rother in shortened.values:
            builder = _Builder(shortened)
            builder.append("*", rhead, rother)
            return result(builder.finish(), "halve_available_factors")
        if other != B:
            raise ArithmeticError("unclassified missing factor root")
        builder, rB = rooted_first_product()
        head = rB
        for _ in range(gap):
            head = builder.append("*", head, head)
        builder.append("*", head, rB)
        return result(builder.finish(), "halve_first_product")

    if B not in (left, right):
        rleft, rright = isqrt(left), isqrt(right)
        if rleft * rleft != left or rright * rright != right:
            raise ArithmeticError("unclassified square of two tower operands")
        builder = _Builder(_prefix(chain, first - 2))
        builder.append("*", rleft, rright)
        return result(builder.finish(), "unused_first_event")

    other = right if left == B else left
    if _power_of_two(B):
        rB, rother = isqrt(B), isqrt(other)
        if rB * rB == B and rother * rother == other:
            builder, _ = rooted_first_product()
            builder.append("*", rB, rother)
            return result(builder.finish(), "halve_two_products")
        return result(doubled_tower_root(), "paired_twos")

    if B != 18 or other != 2 or root != 6:
        raise ArithmeticError("unclassified square from a first-small sum")
    return result(_small_root(6), "exceptional_product")
