"""Exact classification of maximal-energy divisor sets for ICG orders outside the known theorems.

Prints a JSON certificate for every order in ORDERS: 2^a p^b and 3^a p^b with at most 15 cells,
and three- and four-prime orders containing 2 or 3. Symbolic primes p, q range over odd primes
different from the fixed primes. Registered in scripts.check_certificates.
"""

import json

from solved.icg_families import classify


def _two_prime(fixed, max_cells=15):
    return [
        [[fixed, a], ["p", b]]
        for a in range(1, 8)
        for b in range(1, 8)
        if (a + 1) * (b + 1) - 1 <= max_cells
    ]


ORDERS = (
    _two_prime(2)
    + _two_prime(3)
    + [
        [[2, 1], ["p", 1], ["q", 1]],
        [[3, 1], ["p", 1], ["q", 1]],
        [[2, 2], ["p", 1], ["q", 1]],
        [[2, 1], ["p", 2], ["q", 1]],
        [[3, 2], ["p", 1], ["q", 1]],
        [[3, 1], ["p", 2], ["q", 1]],
        [[2, 1], ["p", 3], ["q", 1]],
        [[2, 1], [3, 1], ["p", 1], ["q", 1]],
    ]
)


def main():
    out = []
    for spec in ORDERS:
        factors = [(r if isinstance(r, str) else int(r), a) for r, a in spec]
        out.append({"order": spec, "result": classify(factors)})
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
