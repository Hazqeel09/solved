"""Executable conformance checks for the arithmetic models in the formal proof.

These finite checks do not establish the asymptotic theorem; Lean proves it.
"""

import json
import random

from checks.classical import shortest_chain
from solved.chains import Chain, catalogue, level
from solved.square_controls import encode


def execute(tape, *, signed=False):
    if type(signed) is not bool:
        raise ValueError("signed must be a Boolean")
    tape = tuple(tuple(row) for row in tape)
    values = [1]
    allowed = {"+", "*", "-"} if signed else {"+", "*"}
    for row in tape:
        if len(row) != 3:
            raise ValueError("each instruction needs an operation and two indices")
        op, a, b = row
        if (
            type(op) is not str
            or op not in allowed
            or any(type(i) is not int or not 0 <= i < len(values) for i in (a, b))
        ):
            raise ValueError("invalid arithmetic operation or input reference")
        x, y = values[a], values[b]
        values.append(x + y if op == "+" else x * y if op == "*" else x - y)
    return tuple(values)


def normalize(tape):
    tape = tuple(tuple(row) for row in tape)
    original = execute(tape)
    first = {1: None}
    for value, (op, a, b) in zip(original[1:], tape, strict=True):
        if value not in first:
            first[value] = (op, original[a], original[b])
    values = tuple(sorted(value for value in first if value <= original[-1]))
    index = {1: 0}
    recipes = []
    for value in values[1:]:
        op, a, b = first[value]
        if not a < value or not b < value:
            raise ArithmeticError("a first noninitial occurrence must have smaller operands")
        recipes.append((op, index[a], index[b]))
        index[value] = len(index)
    result = Chain(values, tuple(recipes))
    encode(result)
    if len(result.recipes) > len(tape) or result.values[-1] != original[-1]:
        raise ArithmeticError("normalization changed the endpoint or increased cost")
    return result


def signed_mersenne(n):
    if type(n) is not int or n < 0:
        raise ValueError("nonnegative integer tower index required")
    tape = [("+", 0, 0)]
    for _ in range(n):
        last = len(tape)
        tape.append(("*", last, last))
    tape.append(("-", len(tape), 0))
    return tuple(tape)


def verify():
    rng = random.Random(271127)
    categories = {"programs": 0, "decreasing_write": 0, "duplicate_value": 0, "unused_overshoot": 0}
    seen = set()
    for length in range(13):
        for _ in range(80):
            tape = tuple(
                (rng.choice(("+", "*")), rng.randrange(i + 1), rng.randrange(i + 1))
                for i in range(length)
            )
            if tape in seen:
                continue
            seen.add(tape)
            original = execute(tape)
            normalized = normalize(tape)
            if execute(normalized.recipes) != normalized.values:
                raise ArithmeticError("normalized recipe replay failed")
            categories["programs"] += 1
            categories["decreasing_write"] += any(a > b for a, b in zip(original, original[1:]))
            categories["duplicate_value"] += len(set(original)) < len(original)
            categories["unused_overshoot"] += max(original) > original[-1]
    towers = []
    for n in range(11):
        tape = signed_mersenne(n)
        values = execute(tape, signed=True)
        target = (1 << (1 << n)) - 1
        if values[-1] != target or len(tape) != n + 2:
            raise ArithmeticError("signed tower witness failed")
        towers.append({"n": n, "target_bits": target.bit_length(), "writes": len(tape)})
    negative = execute((("-", 0, 0), ("-", 1, 0), ("*", 2, 2)), signed=True)
    if negative != (1, 0, -1, 1):
        raise ArithmeticError("signed model improperly restricted intermediate values")
    small = []
    for n in range(1, 5):
        target = (1 << (1 << n)) - 1
        minimum = len(shortest_chain(target, product=True)) - 1
        best, _, counts = catalogue(target, minimum - 1 - level(target))
        if target in best:
            raise ArithmeticError("independent finite minimum checks disagree")
        small.append(
            {
                "n": n,
                "am_minimum": minimum,
                "signed_witness_length": n + 2,
                "shorter_chain_counts": counts,
            }
        )
    return {
        "normalization": categories,
        "signed_witnesses": towers,
        "negative_and_zero_trace": negative,
        "small_examples": small,
        "scope": "Finite model checks; the asymptotic result is proved by Lean.",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
