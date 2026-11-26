"""Independent finite-signature verification using normalized exact prime-log coefficients.

No floating-point logarithms or materialized tower endpoints enter this computation.
"""

from fractions import Fraction as Q
from functools import lru_cache
from math import lcm, prod

from solved.seven_steps import catalogue


def lin(x, a, y, b):
    return tuple(i * a + j * b for i, j in zip(x, y))


@lru_cache(maxsize=None)
def comp(x, y):
    diff = tuple(a - b for a, b in zip(x, y))
    den = lcm(*(v.denominator for v in diff))
    exp = [int(den * v) for v in diff]
    lhs = prod(p ** max(e, 0) for p, e in zip((2, 3, 5), exp))
    rhs = prod(p ** max(-e, 0) for p, e in zip((2, 3, 5), exp))
    return (lhs > rhs) - (lhs < rhs)


def independent(initial, count):
    one = (Q(1), Q(0), Q(0))
    z = tuple(Q(0) for _ in one)
    quarter = tuple(v / 4 for v in one)
    init = one if initial == 4 else (Q(0), Q(1, 2), Q(0))
    required = count - (1 if initial == 4 else 2)
    found = set()

    def visit(u, v, w, gaps, dev):
        if len(gaps) == required:
            if comp(u, quarter) >= 0:
                found.add((gaps, dev))
            return
        for gap in (0, 1, 2):
            a, b, c = (u, v, w) if gap == 0 else (u, u, v) if gap == 1 else (u, u, u)
            maximum = lin(a, Q(1, 2), b, Q(1, 4))
            if not gaps and not gap:
                runner = (Q(0), Q(0), Q(1, 4)) if initial == 3 else (Q(1, 4), Q(1, 4), Q(0))
            else:
                left = lin(a, Q(1, 2), c, Q(1, 8))
                right = tuple(v / 2 for v in b)
                runner = left if comp(left, right) >= 0 else right
            for value, index in ((maximum, ()), (runner, (len(gaps) + 1,))):
                if comp(value, quarter) >= 0:
                    visit(value, a, b, (*gaps, gap), dev + index)

    visit(init, one, z, (), ())
    return found


def verify():
    report = catalogue()
    for initial in (3, 4):
        found = independent(initial, 7)
        ref = report["signatures"][str(initial)]
        counts = ref["compressed_survivors_by_deviation_count"]
        if any(sum(len(ds) == j for _, ds in found) != n for j, n in enumerate(counts)):
            raise AssertionError("wrong multiplicity")
        gaps = {tuple(j + 1 for j, x in enumerate(g) if x) for g, ds in found if not ds}
        if gaps != set(ref["maximal_gap_supports"]):
            raise AssertionError("wrong gap family")
        exceptions = {(tuple(r["gaps"]), tuple(r["positions"])) for r in ref["deviation_words"]}
        if {(g, ds) for g, ds in found if ds} != exceptions:
            raise AssertionError("wrong deviations")
        if independent(initial, 8):
            raise AssertionError("eight nonsquares survived")
        print(
            initial, len(found), "admissible compressed signatures; no eighth canonical nonsquare"
        )
    return True


if __name__ == "__main__":
    verify()
