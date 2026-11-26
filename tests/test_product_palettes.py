import random
import unittest
from itertools import combinations, product

from solved.product_palettes import bottleneck, min_cost_narrow, narrow_solutions, solve


class ProductPaletteTests(unittest.TestCase):
    def test_against_all_assignments_and_costs(self):
        rng = random.Random(5361)
        for n in range(6):
            for _ in range(100):
                palettes = [tuple(rng.sample(range(1, 21), rng.randrange(1, 5))) for _ in range(n)]
                edges = []
                for _ in range(2 * n):
                    low = rng.randrange(1, 100)
                    edges.append(
                        (rng.randrange(n), rng.randrange(n), low, low + rng.randrange(100))
                    )
                feasible = [
                    x
                    for x in product(*palettes)
                    if all(a <= x[u] * x[v] <= b for u, v, a, b in edges)
                ]
                got = solve(palettes, edges)
                self.assertEqual(got.values is not None, bool(feasible))
                if feasible:
                    self.assertIn(got.values, feasible)
                costs = [tuple(rng.randrange(5) for _ in row) for row in palettes]
                level, result = bottleneck(palettes, costs, edges)
                expected = min(
                    (
                        max((costs[i][palettes[i].index(v)] for i, v in enumerate(x)), default=0)
                        for x in feasible
                    ),
                    default=None,
                )
                self.assertEqual(level, expected)
                if feasible:
                    self.assertIn(result.values, feasible)

    def test_narrow_enumeration_and_sum_optimum(self):
        rng = random.Random(935)
        for n in range(1, 6):
            for _ in range(60):
                palettes = [tuple(sorted(rng.sample(range(5, 16), 3))) for _ in range(n)]
                truth = [rng.choice(row) for row in palettes]
                pairs = [(i, i + 1) for i in range(n - 1)]
                pairs += [(rng.randrange(n), rng.randrange(n)) for _ in range(2)]
                edges = []
                for u, v in pairs:
                    upper = truth[u] * truth[v] + rng.randrange(4)
                    edges.append((u, v, upper - 3, upper))
                expected = [
                    x
                    for x in product(*palettes)
                    if all(a <= x[u] * x[v] <= b for u, v, a, b in edges)
                ]
                actual = list(narrow_solutions(palettes, edges))
                self.assertEqual(set(actual), set(expected))
                self.assertEqual(len(actual), len(set(actual)))
                costs = [tuple(rng.randrange(8) for _ in row) for row in palettes]
                best, values = min_cost_narrow(palettes, costs, edges)
                minimum = min(
                    (sum(costs[i][palettes[i].index(x[i])] for i in range(n)) for x in expected),
                    default=None,
                )
                self.assertEqual(best, minimum)
                if values is not None:
                    self.assertIn(values, expected)
        with self.assertRaises(ValueError):
            list(narrow_solutions([(1, 2)] * 2, []))
        self.assertEqual(list(narrow_solutions([()], [])), [])
        self.assertEqual(min_cost_narrow([], [], []), (0, ()))

    def test_vertex_cover_cost_embedding(self):
        edges = list(combinations(range(5), 2))
        constraints = [(u, v, 2, 4) for u, v in edges]
        feasible = [
            row for row in product((1, 2), repeat=5) if all(row[u] * row[v] >= 2 for u, v in edges)
        ]
        self.assertEqual(min(row.count(2) for row in feasible), 4)
        self.assertIsNotNone(solve([(1, 2)] * 5, constraints).values)
        self.assertEqual(bottleneck([(1, 2)] * 5, [(0, 1)] * 5, constraints)[0], 1)
        # At width exactly m, low-valued vertices cover every edge. The minimum
        # cost is vertex cover when low costs one and high costs zero.
        m = 10
        boundary = [(u, v, m * m, m * (m + 1)) for u, v in edges]
        models = [
            x
            for x in product((m, m + 1), repeat=5)
            if all(a <= x[u] * x[v] <= b for u, v, a, b in boundary)
        ]
        self.assertEqual(min(x.count(m) for x in models), 4)
        with self.assertRaises(ValueError):
            list(narrow_solutions([(m, m + 1)] * 5, boundary))

    def test_gaps_big_integers_duplicates_and_empty_domains(self):
        n = 10**30
        self.assertEqual(
            solve([(n, n + 5), (n + 7, n + 13)], [(0, 1, n * (n + 7), n * (n + 7))]).values,
            (n, n + 7),
        )
        self.assertEqual(solve([(2, 2), (3, 3)], [(0, 1, 6, 6)]).values, (2, 3))
        self.assertIsNone(solve([()], []).values)
        self.assertIsNone(solve([(1, 2)], [(0, 0, 2, 3)]).values)
        self.assertEqual(solve([(1, 2)], [(0, 0, 4, 4)]).values, (2,))
        self.assertEqual(bottleneck([(2, 2), (3,)], [(9, 1), (0,)], [(0, 1, 6, 6)])[0], 1)

    def test_contracts(self):
        for palettes, edges in [
            ([(True,)], []),
            ([(0,)], []),
            ([(1,)], [(0, 1, 1, 1)]),
            ([(1,)], [(0, 0, 3, 2)]),
        ]:
            with self.assertRaises(ValueError):
                solve(palettes, edges)
        with self.assertRaises(ValueError):
            bottleneck([(1,)], [(True,)], [])
        with self.assertRaises(ValueError):
            bottleneck([(1, 2)], [(1,)], [])
