"""Reproduce an AM squaring counterexample with two different exact searches."""

import argparse
import json
from math import isqrt

from checks.classical import shortest_chain
from solved.chains import catalogue, level

ROOT_CHAIN = (1, 2, 4, 16, 256, 260, 264, 266, 267)
SQUARE_CHAIN = (1, 2, 4, 8, 9, 81, 89, 7921, 71289)


def replay(values):
    if not values or type(values[0]) is not int or values[0] != 1:
        raise ValueError("a chain must start with 1")
    for i, value in enumerate(values[1:], 1):
        if type(value) is not int or value <= values[i - 1]:
            raise ValueError("strictly increasing integer values required")
        if not any(value in (a + b, a * b) for a in values[:i] for b in values[:i]):
            raise ValueError("no legal addition or multiplication recipe")
    return values[-1]


def verify():
    records = []
    for witness in (ROOT_CHAIN, SQUARE_CHAIN):
        n = replay(witness)
        optimum = shortest_chain(n, product=True)
        if len(optimum) != len(witness):
            raise ArithmeticError("witness is not shortest")
        budget = len(witness) - 2
        small = budget - level(n)
        best, _, counts = catalogue(n, small)
        if n in best:
            raise ArithmeticError("independent defect search found a shorter chain")
        records.append(
            {
                "target": n,
                "length": len(witness) - 1,
                "level": level(n),
                "witness": list(witness),
                "excluded_length": budget,
                "lower_bound_small_budget": small,
                "lower_bound_sequence_counts": counts,
            }
        )
    if ROOT_CHAIN[-1] ** 2 != SQUARE_CHAIN[-1]:
        raise ArithmeticError("the two targets are not a square pair")
    return {
        "model": "strictly increasing addition-multiplication chains from 1",
        "cases": records,
        "root_defect": 4,
        "square_defect": 3,
    }


def first_exception(upper=267):
    if type(upper) is not int or upper < 2:
        raise ValueError("integer upper bound at least two required")
    lengths = []
    exceptions = []
    for n in range(2, upper + 1):
        a = len(shortest_chain(n, product=True)) - 1
        b = len(shortest_chain(n * n, product=True)) - 1
        lengths.append([n, a, b])
        if b < a + 1:
            exceptions.append(n)
    return {"range": [2, upper], "lengths": lengths, "exceptions": exceptions}


def power_witness(k):
    """An explicit (k+7)-write construction for 267**(2**k), for every k>=1."""
    if type(k) is not int or k < 1:
        raise ValueError("positive integer squaring count required")
    values = list(SQUARE_CHAIN)
    for _ in range(k - 1):
        values.append(values[-1] ** 2)
    return tuple(values)


def power_minima(max_power=8):
    if type(max_power) is not int or not 1 <= max_power <= 8:
        raise ValueError("this finite census supports powers one through eight")
    witnesses = [power_witness(k) for k in range(1, max_power + 1)]
    best, _, counts = catalogue(witnesses[-1][-1], 2)
    records = []
    for k, witness in enumerate(witnesses, 1):
        n = replay(witness)
        if len(witness) - 1 != k + 7 or level(n) != k + 4 or n in best:
            raise ArithmeticError("power minimum certificate failed")
        if isqrt(n) != 267 ** (1 << (k - 1)):
            raise ArithmeticError("power construction disagrees")
        records.append(
            {"squarings": k, "target_bit_length": n.bit_length(), "minimum_length": k + 7}
        )
    return {"powers": records, "lower_bound_small_budget": 2, "sequence_counts": counts}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--least", action="store_true", help="check every possible smaller positive base"
    )
    parser.add_argument(
        "--powers", action="store_true", help="certify minima through eight squarings"
    )
    args = parser.parse_args()
    result = verify()
    if args.least:
        result["least_exception"] = first_exception()
    if args.powers:
        result["power_minima"] = power_minima()
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
