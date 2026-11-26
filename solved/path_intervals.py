"""Sound inverse intervals and exact guards for bounded unary arithmetic paths."""

from math import isqrt

from .arithmetic import DomainError, calculate
from .product_intervals import Recovery, recover


def _steps(path, limit):
    if type(limit) is not int or limit < 1:
        raise ValueError("positive integer value cap required")
    steps = tuple(tuple(step) for step in path)
    for step in steps:
        if len(step) != 3:
            raise ValueError("path steps are operation, constant or None, and operand order")
        op, constant, reverse = step
        if op not in ("+", "-", "*", "/") or type(reverse) is not bool:
            raise ValueError("invalid arithmetic step")
        if constant is not None and (type(constant) is not int or not 1 <= constant <= limit):
            raise ValueError("path constants must be bounded positive integers")
    return steps


def preimage(path, lower, upper, limit):
    """Inclusive interval containing every legal input. Exact divisions need replay."""
    path = _steps(path, limit)
    if type(lower) is not int or type(upper) is not int:
        raise ValueError("integer observation bounds required")
    lower, upper = max(1, lower), min(limit, upper)
    for op, constant, reverse in reversed(path):
        if lower > upper:
            return None
        if constant is None:
            if op == "+":
                lower, upper = (lower + 1) // 2, upper // 2
            elif op == "*":
                lower, upper = isqrt(lower - 1) + 1, isqrt(upper)
            elif op == "/":
                if not lower <= 1 <= upper:
                    return None
                lower, upper = 1, limit
            else:
                return None
        elif op == "+":
            lower, upper = lower - constant, upper - constant
        elif op == "-":
            lower, upper = (
                (constant - upper, constant - lower)
                if reverse
                else (lower + constant, upper + constant)
            )
        elif op == "*":
            lower, upper = (lower + constant - 1) // constant, upper // constant
        elif reverse:
            lower, upper = (constant + upper - 1) // upper, constant // lower
        else:
            lower, upper = constant * lower, constant * upper
        lower, upper = max(1, lower), min(limit, upper)
    return (lower, upper) if lower <= upper else None


def execute(path, value, limit):
    """Return the output and all paid arithmetic steps, checking every intermediate."""
    path = _steps(path, limit)
    if type(value) is not int or not 1 <= value <= limit:
        raise ValueError("invalid initial path value")
    writes = []
    for op, constant, reverse in path:
        a, b = (
            (value, value)
            if constant is None
            else ((constant, value) if reverse else (value, constant))
        )
        value = calculate(op, a, b, limit)
        writes.append((value, op, a, b))
    return value, tuple(writes)


def recover_paths(domains, observations, limit):
    """Lift narrow-product recovery to edges (u,v,path,output_lower,output_upper)."""
    edges = []
    _steps((), limit)
    observations = tuple(
        (u, v, _steps(path, limit), lower, upper) for u, v, path, lower, upper in observations
    )
    for u, v, path, lower, upper in observations:
        interval = preimage(path, lower, upper, limit)
        if interval is None:
            return Recovery("infeasible", None, (), 0)
        edges.append((u, v, *interval))
    result = recover(domains, edges)
    if result.values is None:
        return result
    if any(value > limit for value in result.values):
        return Recovery("infeasible", None, result.walk, result.evaluations)
    for u, v, path, lower, upper in observations:
        try:
            output, _ = execute(path, result.values[u] * result.values[v], limit)
        except (DomainError, ValueError):
            return Recovery("infeasible", None, result.walk, result.evaluations)
        if not lower <= output <= upper:
            return Recovery("infeasible", None, result.walk, result.evaluations)
    return result
