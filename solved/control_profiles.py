"""Exact symbolic bounds for diagonal families of positive arithmetic controls.

A profile (b_0,...,b_d) represents the upper bound product b_i**(x**i),
where x=2**t and selected square-run lengths all increase by t. The
coefficient at the total number of selected runs supplies a matching leading
lower bound. Bounds use integers only; no floating-point logarithms are used.
"""

from dataclasses import dataclass
from itertools import zip_longest

from .arithmetic import power_capped
from .limits import ResourceLimit
from .square_controls import Description, validate
from .square_exclusions import compare_tower_minus_one


class Arithmetic:
    def __init__(self, max_bits=1_000_000):
        if max_bits is not None and (type(max_bits) is not int or max_bits < 1):
            raise ValueError("a positive bit budget or None is required")
        self.max_bits = max_bits

    def check(self, value):
        if self.max_bits is not None and value.bit_length() > self.max_bits:
            raise ResourceLimit("exact integer exceeds the materialization bit budget")
        return value

    def add(self, a, b):
        return self.check(a + b)

    def multiply(self, a, b):
        if self.max_bits is not None and a.bit_length() + b.bit_length() - 1 > self.max_bits:
            raise ResourceLimit("exact product exceeds the materialization bit budget")
        return self.check(a * b)

    def power(self, value, exponent):
        if value == 1:
            return 1
        if self.max_bits is not None and (value.bit_length() - 1) * exponent >= self.max_bits:
            raise ResourceLimit("exact power exceeds the materialization bit budget")
        return self.check(value**exponent)

    def squares(self, value, count):
        if value == 1:
            return 1
        if self.max_bits is not None and (
            count >= self.max_bits.bit_length()
            or (value.bit_length() - 1) << count >= self.max_bits
        ):
            raise ResourceLimit("square run exceeds the materialization bit budget")
        return self.check(value ** (1 << count))


def _trim(bases):
    bases = tuple(bases)
    while len(bases) > 1 and bases[-1] == 1:
        bases = bases[:-1]
    return bases


@dataclass(frozen=True)
class Profile:
    bases: tuple[int, ...]
    free_count: int

    def __post_init__(self):
        bases = tuple(self.bases)
        if not bases or any(type(b) is not int or b < 1 for b in bases):
            raise ValueError("positive integer coefficient bases required")
        bases = _trim(bases)
        if (
            type(self.free_count) is not int
            or self.free_count < 0
            or len(bases) > self.free_count + 1
        ):
            raise ValueError("invalid free-run dimension")
        object.__setattr__(self, "bases", bases)

    def coefficient(self, degree):
        if type(degree) is not int or degree < 0:
            raise ValueError("nonnegative integer degree required")
        return self.bases[degree] if degree < len(self.bases) else 1

    def upper(self, x, *, max_bits=1_000_000):
        if type(x) is not int or x < 1:
            raise ValueError("positive integer evaluation point required")
        arithmetic = Arithmetic(max_bits)
        result = 1
        power = 1
        for base in self.bases:
            result = arithmetic.multiply(result, arithmetic.power(base, power))
            power = power * x if max_bits is None else min(max_bits, power * min(x, max_bits))
        return result

    def leading_lower(self, x, *, max_bits=1_000_000):
        if type(x) is not int or x < 1:
            raise ValueError("positive integer evaluation point required")
        arithmetic = Arithmetic(max_bits)
        base = self.coefficient(self.free_count)
        if base == 1:
            return 1
        exponent = (
            x**self.free_count if max_bits is None else power_capped(x, self.free_count, max_bits)
        )
        return arithmetic.power(base, exponent)


def _needed(description):
    """Output ancestry only; all instructions still contribute to the charged cost."""
    needed = {len(description.control)}
    for position in range(len(description.control), 0, -1):
        if position in needed:
            op, a, b = description.control[position - 1]
            needed.add(a)
            if op != "squares":
                needed.add(b)
    return needed


def profile(description, free=None, *, max_bits=1_000_000):
    description = validate(description)
    chosen = tuple(range(len(description.runs))) if free is None else tuple(free)
    if any(type(i) is not int or not 0 <= i < len(description.runs) for i in chosen) or len(
        set(chosen)
    ) != len(chosen):
        raise ValueError("distinct valid free-run indices required")
    chosen = set(chosen)
    arithmetic = Arithmetic(max_bits)
    values = [(1,)]
    needed = _needed(description)
    run = 0
    for position, (op, a, b) in enumerate(description.control, 1):
        run_index = run
        if op == "squares":
            run += 1
        if position not in needed:
            values.append(None)
            continue
        left = values[a]
        if left is None:
            raise ArithmeticError("missing output dependency")
        if op == "squares":
            result = tuple(arithmetic.squares(v, description.runs[run_index]) for v in left)
            if run_index in chosen:
                result = (1, *result)
        else:
            right = values[b]
            if right is None:
                raise ArithmeticError("missing output dependency")
            if op == "+" and len(left) == len(right) == 1:
                result = (arithmetic.add(left[0], right[0]),)
            elif op == "+":
                result = tuple(max(x, y) for x, y in zip_longest(left, right, fillvalue=1))
                result = (arithmetic.multiply(2, result[0]), *result[1:])
            else:
                result = tuple(
                    arithmetic.multiply(x, y) for x, y in zip_longest(left, right, fillvalue=1)
                )
        values.append(_trim(result))
    result = Profile(values[-1], len(chosen))
    if len(result.bases) > result.free_count + 1:
        raise ArithmeticError("symbolic degree exceeds the number of free runs")
    return result


def endpoint(description, *, max_bits=1_000_000):
    description = validate(description)
    arithmetic = Arithmetic(max_bits)
    values = [1]
    needed = _needed(description)
    runs = iter(description.runs)
    for position, (op, a, b) in enumerate(description.control, 1):
        count = next(runs) if op == "squares" else None
        if position not in needed:
            values.append(None)
            continue
        if values[a] is None or (op != "squares" and values[b] is None):
            raise ArithmeticError("missing output dependency")
        if op == "squares":
            value = arithmetic.squares(values[a], count)
        elif op == "+":
            value = arithmetic.add(values[a], values[b])
        else:
            value = arithmetic.multiply(values[a], values[b])
        values.append(value)
    return values[-1]


def in_upset(description, excess, *, max_bits=1_000_000):
    description = validate(description)
    if type(excess) is not int or not 0 <= excess <= description.length:
        raise ValueError("excess must give a nonnegative target index")
    value = endpoint(description, max_bits=max_bits)
    return compare_tower_minus_one(value, description.length - excess) <= 0


@dataclass(frozen=True)
class IdealDecision:
    empty: bool
    anchor: Description
    free: tuple[int, ...]
    bound: Profile | None
    witness: tuple[int, ...] | None
    shift: int | None
    method: str
    point_value: int | None = None


def ideal_intersection(base, excess, upper=None, *, max_bits=1_000_000):
    """Decide if the upward set meets a box with finite or infinite upper bounds.

    A nonempty answer carries a symbolic witness. Its membership follows from
    the profile bound without materializing its potentially enormous endpoint.
    """
    base = validate(base)
    if type(excess) is not int or not 0 <= excess <= base.length:
        raise ValueError("base must have a nonnegative target index")
    upper = (None,) * len(base.runs) if upper is None else tuple(upper)
    if len(upper) != len(base.runs) or any(
        u is not None and (type(u) is not int or u < lo) for lo, u in zip(base.runs, upper)
    ):
        raise ValueError("upper bounds must contain the base")
    anchor = Description(
        base.control, tuple(lo if hi is None else hi for lo, hi in zip(base.runs, upper))
    )
    free = tuple(i for i, u in enumerate(upper) if u is None)
    n = anchor.length - excess
    try:
        value = endpoint(anchor, max_bits=max_bits)
    except ResourceLimit:
        if not free:
            raise
    else:
        empty = compare_tower_minus_one(value, n) > 0
        if not free or not empty:
            return IdealDecision(
                empty,
                anchor,
                free,
                None,
                None if empty else anchor.runs,
                None if empty else 0,
                "finite" if not free else "exact_base",
                value,
            )
    bound = profile(anchor, free, max_bits=max_bits)
    leading = bound.coefficient(len(free))
    if compare_tower_minus_one(leading, n) > 0:
        return IdealDecision(True, anchor, free, bound, None, None, "leading_lower")
    # First try a tight integer upper bound on the logarithms. This usually
    # produces a much smaller witness than the general integer-ratio bound.
    lead_log = (leading - 1).bit_length()
    lower_log = sum((bound.coefficient(i) - 1).bit_length() for i in range(len(free)))
    total = lead_log + lower_log
    if n >= max(1, total).bit_length():
        shift = 0
        method = "log_ceiling"
    else:
        difference = (1 << n) - lead_log
        if difference > 0:
            shift = (lower_log // difference).bit_length()
            method = "log_ceiling"
        else:
            # 2**shift >= leading * product(lower bases) follows from bit lengths.
            # Bernoulli's inequality then guarantees strict domination by V**x.
            shift = sum(bound.coefficient(i).bit_length() for i in range(len(free) + 1))
            method = "integer_ratio"
    witness = tuple(value + shift if i in free else value for i, value in enumerate(anchor.runs))
    return IdealDecision(False, anchor, free, bound, witness, shift, method)
