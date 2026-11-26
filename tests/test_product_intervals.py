import random
import unittest
from itertools import product

from solved.product_intervals import recover


class ProductIntervalTests(unittest.TestCase):
    def test_exhaustive_integer_assignments(self):
        rng = random.Random(260811)
        for n in range(1, 6):
            for _ in range(150):
                low = rng.randrange(2, 7)
                domains = [(low, low + rng.randrange(1, 4)) for _ in range(n)]
                if rng.randrange(3) == 0:
                    anchor = rng.randrange(n)
                    domains[anchor] = (low, low)
                pairs = [(i, i + 1) for i in range(n - 1)]
                pairs += [(rng.randrange(n), rng.randrange(n)) for _ in range(3)]
                edges = []
                truth = [rng.randint(a, b) for a, b in domains]
                for u, v in pairs:
                    width = rng.randrange(low)
                    upper = truth[u] * truth[v] + rng.randrange(-1, width + 2)
                    edges.append((u, v, max(1, upper - width), upper))
                possible = [
                    row
                    for row in product(*(range(a, b + 1) for a, b in domains))
                    if all(a <= row[u] * row[v] <= b for u, v, a, b in edges)
                ]
                result = recover(domains, edges)
                if result.status == "undetermined":
                    continue
                self.assertLessEqual(len(possible), 1)
                self.assertEqual(result.values, possible[0] if possible else None)
                self.assertEqual(result.status, "unique" if possible else "infeasible")

    def test_large_odd_cycles_and_anchored_trees(self):
        values = (10**12 + 39, 10**13 + 7, 10**11 + 11, 10**12 + 333, 10**13 + 141)
        edges = [
            (
                i,
                (i + 1) % 5,
                values[i] * values[(i + 1) % 5] - 10000,
                values[i] * values[(i + 1) % 5] + 9999,
            )
            for i in range(5)
        ]
        result = recover([(20000, 10**18)] * 5, edges)
        self.assertEqual(result.values, values)
        self.assertLessEqual(result.evaluations, 62)
        domains = [(20000, 10**18)] * 5
        domains[3] = (values[3], values[3])
        self.assertEqual(recover(domains, edges[:4]).values, values)
        self.assertEqual(recover([(2, 3)] * 2, [(0, 1, 6, 6)]).status, "undetermined")

    def test_sharp_threshold_and_clamped_false_fixed_point(self):
        # At width M, two triangle assignments exist even with all factors >= M.
        M = 10
        edges = [(0, 1, 100, 110), (0, 2, 100, 110), (1, 2, 100, 100)]
        self.assertTrue(
            all(a <= x[u] * x[v] <= b for x in ((10, 10, 10), (11, 10, 10)) for u, v, a, b in edges)
        )
        with self.assertRaises(ValueError):
            recover([(M, M + 1)] * 3, edges)
        self.assertEqual(recover([(10, 12)], [(0, 0, 110, 110)]).status, "infeasible")
        self.assertEqual(recover([(10, 12)], [(0, 0, 121, 121)]).values, (11,))
        self.assertEqual(recover([(5, 5)], []).values, (5,))

    def test_input_contract(self):
        for domains, edges in [
            ([], []),
            ([(True, 3)], []),
            ([(2, 1)], []),
            ([(2, 4)], [(0, 1, 4, 4)]),
            ([(2, 4)], [(0, 0, 0, 4)]),
            ([(2, 4)] * 2, []),
            ([(2, 4)], [(0, 0, 4, 6)]),
        ]:
            with self.assertRaises(ValueError):
                recover(domains, edges)
