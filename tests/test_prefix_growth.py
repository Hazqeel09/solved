import unittest
from itertools import combinations_with_replacement

from checks.verify_prefix_growth import compare
from solved.prefix_growth import completion_max, increment_max


class PrefixGrowthTests(unittest.TestCase):
    def test_endpoints_and_increments_by_exhaustion(self):
        for prefix in ((1, 2, 3), (1, 2, 4), (1, 2, 3, 5), (1, 2, 4, 5, 6), (1, 2, 4, 8, 16)):
            observed = {}

            def visit(row, b, d):
                m = row[-1]
                values = {
                    v
                    for a, c in combinations_with_replacement(row, 2)
                    for v in (a + c, a * c)
                    if v > m
                }
                largest, sq, ns = observed.get((b, d), (0, 0, 0))
                observed[b, d] = (
                    max(largest, m),
                    max(sq, m * m - m),
                    max(ns, max(v - m for v in values if v != m * m)),
                )
                if b + d < 4:
                    for v in values:
                        visit(row + (v,), b + int(v != m * m), d + int(v == m * m))

            visit(prefix, 0, 0)
            for (b, d), (target, sq, ns) in observed.items():
                args = (*prefix[-2:], b, d)
                self.assertEqual(completion_max(*args), target, args)
                self.assertEqual(increment_max(*args, next_square=True), sq, args)
                self.assertEqual(increment_max(*args, next_square=False), ns, args)
                for clip in (1, target - 1, target, target + 1):
                    self.assertEqual(completion_max(*args, ceiling=clip), min(clip, target), args)

    def test_invalid_and_saturating(self):
        for args in ((1, 2, 1, 2), (2, 2, 0, 0), (2, 5, 0, 1), (2, 3, -1, 0), (2, 3, 0, True)):
            with self.assertRaises(ValueError):
                completion_max(*args)
            with self.assertRaises(ValueError):
                increment_max(*args, next_square=True)
        for cap in (0, False, 2.0):
            with self.assertRaises(ValueError):
                completion_max(2, 3, 1, 1, ceiling=cap)
        with self.assertRaises(ValueError):
            increment_max(2, 3, 0, 0, next_square=1)
        self.assertEqual(completion_max(2, 3, 10**9, 10**9, ceiling=100), 100)

    def test_search_arms(self):
        report = compare(64, repeats=1)
        arms = report["arms"]
        self.assertLess(arms["current_prefix"]["expanded"], arms["squares"]["expanded"])
        self.assertLessEqual(arms["current_prefix"]["expanded"], arms["paper_initial"]["expanded"])
