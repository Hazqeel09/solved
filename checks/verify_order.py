"""Test the normalized polynomial and initial-segment inequality using exact arithmetic."""

import json
from collections import Counter
from fractions import Fraction

from solved.chains import Chain, chains, level
from solved.fixed_defect import decode, encode, radius
from solved.normalized_mass import normalized


def test_chain(c, s):
    m = normalized(c, s)
    v = c.values[-1]
    r = m.writes
    if m.restore() != v or decode(encode(c, s)) != v:
        raise ArithmeticError("endpoint mismatch")
    if r:
        units = 1 << (r - 1)
        two = Fraction(units, 1 << len(m.atoms))
        ratio = Fraction(1)
        for typ, x, den in m.atoms:
            if typ == "mul":
                two += Fraction(units, den)
            else:
                if units % den:
                    raise ArithmeticError("nonintegral logarithmic multiplier")
                ratio *= x ** (units // den)
        if two.denominator != 1 or v > ratio * (1 << two.numerator):
            raise ArithmeticError("initial-segment inequality failed")
    return len(m.atoms)


def reset_families(s):
    # Keep the longest inputs manageable while forcing resets outside the bounded prefix.
    from itertools import product

    for ops in product(("+", "*"), repeat=s):
        values = [1, 2]
        recipes = [("+", 0, 0)]

        def put(op, a, b):
            values.append(values[a] + values[b] if op == "+" else values[a] * values[b])
            recipes.append((op, a, b))

        while len(recipes) <= radius(s):
            put("*", len(values) - 1, len(values) - 1)
        for j, op in enumerate(ops):
            put("*", len(values) - 1, len(values) - 1)
            # A multiplication by 2 or an addition of the initial 1 is always legal.
            put(op, len(values) - 1, 1 if op == "*" else 0)
        yield Chain(tuple(values), tuple(recipes))


def main():
    by = Counter()
    atoms = Counter()
    for s, c in chains(10000, 3):
        by[s] += 1
        atoms[test_chain(c, s)] += 1
    targeted = []
    for s in range(1, 4):
        for c in reset_families(s):
            if len(c.recipes) - level(c.values[-1]) > s:
                raise ArithmeticError("bad targeted fixture")
            e = test_chain(c, s)
            if e != s:
                raise ArithmeticError("did not exercise maximal reset count")
            targeted.append({"small_steps": s, "resets": e, "end_bits": c.values[-1].bit_length()})
    print(
        json.dumps(
            {
                "exhaustive_limit": 10000,
                "chains_by_defect": by,
                "low_cap_reset_counts": atoms,
                "targeted_controls": targeted,
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
