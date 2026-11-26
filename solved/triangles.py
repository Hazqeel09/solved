"""Direct formulae for blind three-output proposals on three unknown helper values."""

from collections import Counter
from itertools import combinations
from math import isqrt


def triangle_votes(targets, limit):
    """Return counts of distinct legal target-triple/template witnesses per helper.

    Different templates can explain the same triple. All three output nodes are distinct.
    Python's larger intermediate integers here are work done by the solver, not arithmetic writes.
    """
    if type(limit) is not int or limit < 1:
        raise ValueError("invalid value limit")
    distinct = set()
    for target in targets:
        if type(target) is not int or not 1 <= target <= limit:
            raise ValueError("invalid bounded target")
        distinct.add(target)
    ts = sorted(distinct)
    votes = Counter()

    def emit(x, y, z):
        if 1 <= min(x, y, z) and max(x, y, z) <= limit:
            votes.update({x, y, z})

    for a, b, c in combinations(ts, 3):
        # Three pair sums, then three pair products; output permutation just renames vertices.
        x, rem = divmod(a + b - c, 2)
        if not rem:
            emit(x, a - x, b - x)
        q, rem = divmod(a * b, c)
        if not rem:
            x = isqrt(q)
            if x and x * x == q and a % x == b % x == 0:
                emit(x, a // x, b // x)
        for s, p, q in ((a, b, c), (b, a, c), (c, a, b)):
            # The two products are x*z and y*z. The remaining target is x+y or |x-y|.
            for numerator in (p + q, abs(p - q)):
                z, rem = divmod(numerator, s)
                if z and not rem and p % z == q % z == 0:
                    emit(p // z, q // z, z)
    return votes
