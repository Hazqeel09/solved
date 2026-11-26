import itertools
import unittest
from collections import Counter

from solved.cycles import Edge, solve
from solved.triangles import triangle_votes


def generic(targets, cap):
    votes = Counter()
    for a, b, c in itertools.combinations(sorted(set(targets)), 3):
        patterns = [("+", "+", "+", a, b, c), ("*", "*", "*", a, b, c)]
        for s, p, q in ((a, b, c), (b, a, c), (c, a, b)):
            patterns.extend((("*", "*", "+", p, q, s), ("*", "*", "-", q, p, s)))
        for left, right, end, p, q, s in patterns:
            result = solve((Edge(0, 2, left, p), Edge(1, 2, right, q), Edge(0, 1, end, s)), (), cap)
            for v in result.assignments:
                votes.update(set(v))
    return votes


class TriangleTests(unittest.TestCase):
    def test_all_triples_at_small_caps(self):
        for cap in range(3, 15):
            for ts in itertools.combinations(range(1, cap + 1), 3):
                self.assertEqual(triangle_votes(ts, cap), generic(ts, cap))

    def test_limits_and_cost_overflow(self):
        self.assertFalse(triangle_votes([], 1))
        with self.assertRaises(ValueError):
            triangle_votes([1, True], 10)
        p, q, r = 999_999_937, 999_999_929, 999_999_893
        votes = triangle_votes([p * q, q * r, r * p], 10**18)
        self.assertTrue({p, q, r} <= votes.keys())
        self.assertEqual(triangle_votes([3, 5, 3, 6], 9), triangle_votes([3, 5, 6], 9))
