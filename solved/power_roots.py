"""Root all-power-of-two AM histories via classical low-step addition chains.

The completeness dependency is Knuth's two-small-step classification, as
stated in Altman's thesis, Theorem 4.7.2. It is not inferred from tests.
"""

from .chains import Chain, _ChainBuilder, level
from .limits import ResourceLimit
from .square_controls import encode


def low_step_addition_chain(target):
    """Construct a shortest addition chain when its small-step count is <=2.

    None means the target is outside the cited classical classification,
    not that addition-chain synthesis is impossible. No search is used.
    """
    if type(target) is not int or target < 1:
        raise ValueError("a positive integer target is required")
    if target.bit_count() > 4:
        return None
    positions, remaining = [], target
    while remaining:
        low = remaining & -remaining
        positions.append(low.bit_length() - 1)
        remaining -= low
    bits = tuple(positions)
    builder = _ChainBuilder(Chain((1,), ()))

    def shift(count):
        for _ in range(count):
            head = builder.values[-1]
            builder.append("+", head, head)

    if len(bits) <= 3:
        for bit in bin(target)[3:]:
            shift(1)
            if bit == "1":
                builder.append("+", builder.values[-1], 1)
    elif len(bits) == 4:
        a, b, c, d = bits
        if (b, c, d) == (a + 1, a + 2, a + 7):
            # The exceptional 135 family, then a trailing binary scaling.
            for left, right in (
                (1, 1),
                (1, 2),
                (3, 3),
                (6, 6),
                (3, 12),
                (15, 15),
                (30, 30),
                (60, 60),
                (15, 120),
            ):
                builder.append("+", left, right)
        elif b == a + 1 and d == c + 3:
            # 3(1+3*2^(c-a)). Retain the odd intermediate when multiplying by 3.
            builder.append("+", 1, 1)
            builder.append("+", 1, 2)
            shift(c - a)
            odd = builder.append("+", builder.values[-1], 1)
            shift(1)
            builder.append("+", builder.values[-1], odd)
        elif d == b + c - a:
            # (1+2^(b-a))(1+2^(c-a)).
            shift(b - a)
            factor = builder.append("+", builder.values[-1], 1)
            shift(c - a)
            builder.append("+", builder.values[-1], factor)
        elif d == b + c - a + 1:
            # Retain u=1+2^(b-a); shift v=1+2^(b-a+1), then add u.
            shift(b - a)
            power = builder.values[-1]
            u = builder.append("+", power, 1)
            builder.append("+", u, power)
            shift(c - a)
            builder.append("+", builder.values[-1], u)
        else:
            return None
        shift(a)
    else:
        return None
    chain = builder.finish()
    encode(chain)
    expected = target.bit_length() - 1 + min(len(bits) - 1, 2)
    if chain.values[-1] != target or len(chain.recipes) != expected:
        raise ArithmeticError("low-step addition construction failed its certificate")
    if sum(y != 2 * x for x, y in zip(chain.values, chain.values[1:])) > 3:
        raise ArithmeticError("the low-step normal form has too many nondoublings")
    return chain


def binary_exponents(chain):
    """Translate a validated power-only AM chain into an addition chain."""
    if not isinstance(chain, Chain):
        raise ValueError("an AM chain is required")
    encode(chain)
    if len(chain.values) < 2 or any(v & (v - 1) for v in chain.values):
        raise ValueError("a nontrivial power-of-two history is required")
    exponents = tuple(v.bit_length() - 1 for v in chain.values[1:])
    recipes = []
    for op, a, b in chain.recipes[1:]:
        if op == "*":
            recipes.append(("+", a - 1, b - 1))
        else:
            # A sum of two powers of two is a power of two only for equal inputs.
            if chain.values[a] != chain.values[b]:
                raise ArithmeticError("unequal powers have a power-of-two sum")
            recipes.append(("+", a - 1, 0))
    result = Chain(exponents, tuple(recipes))
    encode(result)
    return result


def lift_binary_powers(chain, *, max_bits):
    """Compile to powers of two, charging the initial 2 write.

    The caller supplies an explicit output-size budget because exponentiation
    can make even a short input chain infeasible to materialize.
    """
    if not isinstance(chain, Chain):
        raise ValueError("an addition chain is required")
    encode(chain)
    if any(op != "+" for op, _, _ in chain.recipes):
        raise ValueError("only addition instructions can be lifted")
    if type(max_bits) is not int or max_bits < 1:
        raise ValueError("a positive integer output bit budget is required")
    if chain.values[-1] + 1 > max_bits:
        raise ResourceLimit("the power lift exceeds the output bit budget")
    result = Chain(
        (1, *(1 << value for value in chain.values)),
        (("+", 0, 0), *(("*", a + 1, b + 1) for _, a, b in chain.recipes)),
    )
    encode(result)
    return result


def reduce_power_square(chain):
    """Shorten a square root of a power-only AM history of defect at most two.

    The endpoint must exceed 1. The whole history, not only its endpoint,
    must consist of powers of two. Every returned instruction is charged.
    """
    exponents = binary_exponents(chain)
    exponent = exponents.values[-1]
    if exponent % 2 or len(chain.recipes) - level(chain.values[-1]) > 2:
        raise ValueError("an even exponent and at most two small steps are required")
    shortened = low_step_addition_chain(exponent // 2)
    if shortened is None:
        raise ArithmeticError("the source contradicts the low-step addition classification")
    result = lift_binary_powers(shortened, max_bits=chain.values[-1].bit_length())
    if result.values[-1] ** 2 != chain.values[-1] or len(result.recipes) >= len(chain.recipes):
        raise ArithmeticError("power-root construction failed its certificate")
    return result
