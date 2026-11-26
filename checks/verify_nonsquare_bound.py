"""Exact finite cross-checks for the formal Fibonacci envelope and control inflation."""

import argparse
import json
from collections import Counter

from solved.chains import chains, level
from solved.square_controls import Description, encode


def below_power_of_two(value, exponent):
    if any(type(v) is not int or v < 0 for v in (value, exponent)):
        raise ValueError("nonnegative integer arguments required")
    leading = value.bit_length() - 1
    return leading < exponent or (leading == exponent and value & (value - 1) == 0)


def check_chain(chain):
    description = encode(chain)  # Reuse the exact chain and operand validation.
    writes = len(chain.recipes)
    if description.length != writes:
        raise ArithmeticError("description cost disagrees")
    if writes == 0:
        return 0, 0
    nonsquares = sum(b != a * a for a, b in zip(chain.values, chain.values[1:]))
    b = nonsquares - 1
    d = writes - nonsquares
    previous, current = 1, 1
    for _ in range(b):
        previous, current = current, previous + current
    if current > 1 << (b - b // 4):
        raise ArithmeticError("four-step Fibonacci bound failed")
    if not below_power_of_two(chain.values[-1], (1 << d) * current):
        raise ArithmeticError("head envelope failed")
    if not below_power_of_two(chain.values[-2], (1 << d) * previous):
        raise ArithmeticError("previous-value envelope failed")
    defect = writes - level(chain.values[-1])
    if nonsquares > 4 * defect + 4:
        raise ArithmeticError("canonical nonsquare count bound failed")
    if len(description.control) > 3 * nonsquares + 1 or len(description.runs) > 2 * nonsquares + 1:
        raise ArithmeticError("finite-control size bound failed")
    return defect, nonsquares


def marked_evaluate(description):
    """Execute the marked description with newest-first saved histories, as in Lean."""
    if not isinstance(description, Description):
        raise ValueError("a marked description is required")
    history = [1]
    parameters = iter(description.runs)
    cost = 0
    for position, (op, left, right) in enumerate(description.control):
        # The existing encoder uses chronological mark IDs; Lean uses offsets
        # from the most recently stored mark. Neither depends on square lengths.
        if type(left) is not int or not 0 <= left <= position:
            raise ValueError("invalid saved operand")
        a = position - left
        if op == "squares":
            count = next(parameters, None)
            if right is not None or type(count) is not int or count < 1:
                raise ValueError("positive square-run length required")
            value = history[a] ** (1 << count)
            cost += count
        else:
            if op not in ("+", "*") or type(right) is not int or not 0 <= right <= position:
                raise ValueError("invalid marked operation")
            b = position - right
            value = history[a] + history[b] if op == "+" else history[a] * history[b]
            cost += 1
        history.insert(0, value)
    sentinel = object()
    if next(parameters, sentinel) is not sentinel:
        raise ValueError("unused square-run length")
    return history[0], cost


def census(limit=10**6, small=3):
    histogram = Counter()
    maximum = Counter()
    for _, chain in chains(limit, small):
        defect, nonsquares = check_chain(chain)
        histogram[defect] += 1
        maximum[defect] = max(maximum[defect], nonsquares)
    return {
        "limit": limit,
        "small_step_budget": small,
        "chains_by_defect": dict(sorted(histogram.items())),
        "maximum_nonsquares_by_defect": dict(sorted(maximum.items())),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=10**6)
    parser.add_argument("--small", type=int, default=3)
    args = parser.parse_args()
    print(json.dumps(census(args.limit, args.small), indent=2))


if __name__ == "__main__":
    main()
