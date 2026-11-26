"""Bounded positive integer arithmetic used by the mathematical verifiers."""

from functools import lru_cache


class DomainError(ValueError):
    """An operation leaves the stated positive exact-integer domain."""


def power_capped(base, exponent, cap):
    """Return min(base**exponent, cap) without materializing a large power."""
    if (
        any(type(v) is not int for v in (base, exponent, cap))
        or base < 0
        or exponent < 0
        or cap < 1
    ):
        raise ValueError("nonnegative integer base/exponent and positive cap required")
    result = 1
    base = min(base, cap)
    while exponent:
        if exponent & 1:
            result = min(cap, result * base)
        exponent >>= 1
        if exponent:
            base = min(cap, base * base)
    return min(result, cap)


def _inputs(a, b, limit):
    if (
        type(limit) is not int
        or limit < 1
        or any(type(v) is not int or not 1 <= v <= limit for v in (a, b))
    ):
        raise DomainError("operands and limit must be bounded positive integers")


def calculate(op, a, b, limit):
    _inputs(a, b, limit)
    if op == "+":
        value = a + b
    elif op == "-":
        value = a - b
    elif op == "*":
        value = a * b
    elif op == "/" and a % b == 0:
        value = a // b
    else:
        raise DomainError("unknown operation or inexact division")
    if not 1 <= value <= limit:
        raise DomainError("intermediate outside the value interval")
    return value


def canonical(op, a, b):
    return (op, min(a, b), max(a, b)) if op in ("+", "*") else (op, a, b)


def binary_results(a, b, limit):
    _inputs(a, b, limit)
    hi, lo = max(a, b), min(a, b)
    if hi + lo <= limit:
        yield hi + lo, ("+", lo, hi)
    if hi > lo:
        yield hi - lo, ("-", hi, lo)
    if hi * lo <= limit:
        yield hi * lo, ("*", lo, hi)
    if hi % lo == 0:
        yield hi // lo, ("/", hi, lo)


def missing_operand(target, known, limit):
    _inputs(target, known, limit)
    offers = [
        (target - known, ("+", target - known, known)),
        (target + known, ("-", target + known, known)),
        (known - target, ("-", known, known - target)),
        (target * known, ("/", target * known, known)),
    ]
    if target % known == 0:
        offers.append((target // known, ("*", target // known, known)))
    if known % target == 0:
        offers.append((known // target, ("/", known, known // target)))
    return [(v, canonical(*rule)) for v, rule in offers if 1 <= v <= limit]


@lru_cache(maxsize=4096, typed=True)
def bounded_divisors(value):
    """Complete divisor list for the verifier's stated input range [1, 10**18]."""
    if type(value) is not int or not 1 <= value <= 10**18:
        raise ValueError("factorization input must lie in [1, 10**18]")
    from sympy import divisors

    result = tuple(int(d) for d in divisors(value))
    if not result or result[0] != 1 or result[-1] != value or any(value % d for d in result):
        raise ArithmeticError("invalid divisor enumeration")
    return result
