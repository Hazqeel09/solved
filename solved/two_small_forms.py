"""Generate two-small-step AM value chains by their nonsquare events and gap intervals."""

from bisect import bisect_left, bisect_right
from dataclasses import dataclass
from math import gcd, isqrt

from .chains import Chain, level


@dataclass(frozen=True)
class Block:
    gap: int
    value: int
    op: str
    left: int
    right: int
    family: str


def gap_cutoff(head, upper, operand, max_gap):
    """Largest admissible g>=1, clipped to max_gap. Zero denotes an empty initial interval."""
    if any(type(v) is not int for v in (head, upper, operand, max_gap)) or not (
        1 < head < upper and operand >= 2 and max_gap >= 0
    ):
        raise ValueError("invalid gap parameters")
    common = gcd(head, upper)
    num, den = upper // common, head // common
    for g in range(1, max_gap + 1):
        num *= num
        den *= den
        if num > operand * den:
            return g - 1
    return max_gap


def square_run(head, limit):
    if type(head) is not int or head < 2 or type(limit) is not int or limit < 1:
        raise ValueError("square runs require head >= 2 and a positive integer cap")
    values = []
    last_base = isqrt(limit)
    while head <= last_base:
        head *= head
        values.append(head)
    return tuple(values)


def immediate(prefix, upper, limit, small):
    m = prefix[-1]
    low = m + 1 if small else upper
    high = min(limit, upper - 1 if small else m * m - 1)
    if low > high:
        return
    for op in ("+", "*"):
        least = (low + 1) // 2 if op == "+" else isqrt(low - 1) + 1
        for j in range(bisect_left(prefix, least), len(prefix)):
            u = prefix[j]
            if op == "+":
                lower, higher = low - u, high - u
            else:
                lower, higher = (low + u - 1) // u, high // u
            for i in range(
                bisect_left(prefix, lower, 0, j + 1), bisect_right(prefix, higher, 0, j + 1)
            ):
                v = u + prefix[i] if op == "+" else u * prefix[i]
                yield Block(0, v, op, i, j, "immediate")


def blocks(prefix, run, upper, limit, small):
    """prefix is valid, its head is >=3, and run lists the feasible following squares."""
    m = prefix[-1]
    yield from immediate(prefix, upper, limit, small)
    bound = len(run)
    if bound == 0:
        return
    old_cuts = {w: gap_cutoff(m, upper, w, bound) for w in set(prefix[1:]) | {2}}
    for g, head in enumerate(run, 1):
        j = len(prefix) + g - 1
        if small:
            earlier = prefix + run[: g - 1]
            for i in range(bisect_right(earlier, limit - head)):
                yield Block(g, head + earlier[i], "+", i, j, "proper_addition")
        if (g > old_cuts[2]) == small and 2 * head <= limit:
            yield Block(g, head + head, "+", j, j, "doubling")
        for i in range(1, bisect_right(prefix, limit // head)):
            w = prefix[i]
            if (g > old_cuts[w]) == small:
                yield Block(g, head * w, "*", i, j, "old_multiplier")
        for lag in range(1, g):
            if (lag > old_cuts[m]) == small:
                w = run[g - lag - 1]
                if head * w <= limit:
                    yield Block(g, head * w, "*", j - lag, j, "run_multiplier")


def two_small_chains(limit):
    """Enumerate each classified value sequence up to an inclusive magnitude cap."""
    if type(limit) is not int or limit < 1:
        raise ValueError("expected positive integer limit")
    if limit < 3:
        return

    def visit(values, recipes, spent, big_events, big_limit):
        m = values[-1]
        run = square_run(m, limit)
        # The single remaining length parameter after the last event.
        if spent == 2:
            yield Chain(values, recipes)
            tail, proof = values, recipes
            for v in run:
                i = len(tail) - 1
                tail += (v,)
                proof += (("*", i, i),)
                yield Chain(tail, proof)
        upper = 1 << (1 << level(m))
        for small in (True, False):
            if small and spent == 2:
                continue
            if not small and (big_events >= big_limit or (spent == 1 and big_events >= 2)):
                continue
            seen = set()
            for step in blocks(values, run, upper, limit, small):
                key = (step.gap, step.value)
                if key in seen:
                    continue
                seen.add(key)
                squares = tuple(
                    ("*", i, i) for i in range(len(values) - 1, len(values) - 1 + step.gap)
                )
                yield from visit(
                    values + run[: step.gap] + (step.value,),
                    recipes + squares + ((step.op, step.left, step.right),),
                    spent + int(small),
                    big_events + int(not small),
                    3 if small and big_events == 0 else big_limit,
                )

    tower, proof = (1, 2), (("+", 0, 0),)
    while True:
        head = tower[-1]
        offered = set()
        for step in immediate(tower, head * head, limit, True):
            if step.value not in offered:
                offered.add(step.value)
                yield from visit(
                    tower + (step.value,), proof + ((step.op, step.left, step.right),), 1, 0, 4
                )
        if head > isqrt(limit):
            break
        i = len(tower) - 1
        tower += (head * head,)
        proof += (("*", i, i),)
