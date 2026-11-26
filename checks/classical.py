"""Small, reproducible witnesses for subtraction, Scholz–Brauer and periodic density."""

import json
from fractions import Fraction
from itertools import combinations_with_replacement


def shortest_chain(n, product=False, star=False, *, admissible=None, counts=None):
    """Iterative deepening over increasing value chains, with an admissible growth bound."""
    if type(n) is not int or n < 1:
        raise ValueError("positive target required")

    def search(row, left):
        if counts is not None:
            counts["visited"] += 1
        last = row[-1]
        if last == n:
            return row
        if not left:
            return None
        upper = last
        for _ in range(left):
            upper = max(2 * upper, upper * upper) if product else 2 * upper
            if upper >= n:
                break
        if upper < n:
            return None
        if admissible is not None and not admissible(row, left):
            return None
        if counts is not None:
            counts["expanded"] += 1
        pairs = ((last, b) for b in row) if star else combinations_with_replacement(row, 2)
        options = set()
        for a, b in pairs:
            options.add(a + b)
            if product:
                options.add(a * b)
        for v in sorted((v for v in options if last < v <= n), reverse=True):
            result = search(row + (v,), left - 1)
            if result:
                return result
        return None

    depth = 0
    while True:
        witness = search((1,), depth)
        if witness:
            return witness
        depth += 1


def mersenne_chain(exponents):
    if not exponents or exponents[0] != 1:
        raise ValueError("start from exponent 1")
    values = [1]
    for i, (a, v) in enumerate(zip(exponents, exponents[1:]), 1):
        b = v - a
        if b not in exponents[:i]:
            raise ValueError("expected a star addition chain")
        # Each appended value is the sum of two entries already built.
        for _ in range(b):
            values.append(values[-1] * 2)
        values.append(values[-1] + (1 << b) - 1)
    return values


def periodic_density(bits):
    """Density for B with membership bits repeating from n=1 onward."""
    if not bits or any(type(b) is not bool for b in bits):
        raise ValueError("nonempty Boolean period required")
    return min(Fraction(sum(bits[:k]), k) for k in range(1, len(bits) + 1))


def expanded_lower_bound(bits):
    """Exact Schnirelmann density of (B∪{0})+{0,1}, treating zero separately."""
    periodic_density(bits)
    q = len(bits)
    expanded = [b or bits[(i - 1) % q] for i, b in enumerate(bits)]
    # n=1 also follows 0 regardless of B's periodic residue zero.
    actual = [True] + expanded[1:]
    # Along any residue class the prefix ratio is between its first value and
    # the limiting mean, since every additional period contributes the same counts.
    first_period = (Fraction(sum(actual[:r]), r) for r in range(1, q + 1))
    return min(Fraction(sum(expanded), q), *first_period)


def main():
    checks = []
    for n in range(1, 60):
        exact = shortest_chain(n)
        star = shortest_chain(n, star=True)
        result = mersenne_chain(star)
        if (
            len(exact) != len(star)
            or len(result) - 1 != n - 1 + len(exact) - 1
            or result[-1] != 2**n - 1
        ):
            raise AssertionError("finite construction failed")
        seen = set()
        for v in result:
            if seen and not any(v - a in seen for a in seen):
                raise AssertionError("invalid chain")
            seen.add(v)
        checks.append(
            {
                "n": n,
                "shortest_addition_length": len(exact) - 1,
                "star": star,
                "mersenne_writes": len(result) - 1,
            }
        )
    print(
        json.dumps(
            {"am_255": shortest_chain(255, product=True), "scholz_range": checks},
            indent=2,
        )
    )


if __name__ == "__main__":
    main()
