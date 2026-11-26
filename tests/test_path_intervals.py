import random
import unittest
from itertools import product

from solved.arithmetic import DomainError
from solved.path_intervals import execute, preimage, recover_paths


class PathIntervalTests(unittest.TestCase):
    def test_backward_bounds_against_all_inputs(self):
        rng = random.Random(193127)
        for _ in range(1600):
            cap = rng.randrange(1, 40)
            path = tuple(
                (
                    rng.choice("+-*/"),
                    None if rng.randrange(4) == 0 else rng.randint(1, cap),
                    bool(rng.randrange(2)),
                )
                for _ in range(rng.randrange(5))
            )
            low = rng.randrange(-3, cap + 3)
            high = low + rng.randrange(cap + 4)
            true = set()
            for value in range(1, cap + 1):
                try:
                    out, _ = execute(path, value, cap)
                except DomainError:
                    continue
                if low <= out <= high:
                    true.add(value)
            bounds = preimage(path, low, high, cap)
            covered = set(range(bounds[0], bounds[1] + 1)) if bounds else set()
            self.assertTrue(true <= covered, (path, cap, low, high, true, bounds))
            if all(op != "/" for op, _, _ in path):
                self.assertEqual(true, covered)

    def test_exact_division_and_overflow_cannot_cancel(self):
        path = (("/", 2, False), ("*", 2, False))
        self.assertEqual(preimage(path, 2, 4, 10), (2, 4))
        with self.assertRaises(DomainError):
            execute(path, 3, 10)
        self.assertEqual(recover_paths([(5, 5)], [(0, 0, path, 24, 26)], 100).status, "infeasible")
        self.assertIsNone(preimage((("*", 2, False), ("/", 2, False)), 9, 9, 10))
        self.assertEqual(preimage((("/", None, False),), 1, 1, 10), (1, 10))
        self.assertIsNone(preimage((("-", None, False),), 1, 10, 10))

    def test_path_factor_recovery_against_exhaustive_assignments(self):
        rng = random.Random(2523)
        for _ in range(180):
            domains = [(7, 10)] * 3
            truth = [rng.randint(7, 10) for _ in domains]
            observations = []
            for u, v in ((0, 1), (1, 2), (2, 0)):
                k = rng.randint(2, 5)
                path = (("*", k, False), ("+", k, False))
                target = truth[u] * truth[v] * k + k + rng.randint(-2, 2)
                observations.append((u, v, path, target - 2, target + 2))
            possible = []
            for row in product(range(7, 11), repeat=3):
                if all(
                    lo <= execute(path, row[u] * row[v], 1000)[0] <= hi
                    for u, v, path, lo, hi in observations
                ):
                    possible.append(row)
            result = recover_paths(domains, observations, 1000)
            self.assertLessEqual(len(possible), 1)
            self.assertEqual(result.values, possible[0] if possible else None)

    def test_iterable_paths_are_preserved_for_exact_replay(self):
        path = (step for step in (("/", 2, False), ("*", 2, False)))
        self.assertEqual(recover_paths([(5, 5)], [(0, 0, path, 24, 26)], 100).status, "infeasible")
        with self.assertRaises(ValueError):
            recover_paths([(2, 2)], [], 0)
        self.assertEqual(recover_paths([(5, 5)], [], 4).status, "infeasible")

    def test_repeated_squares_and_invalid_inputs(self):
        path = (("*", None, False), ("*", None, False))
        self.assertEqual(preimage(path, 10**18, 10**18, 10**18), None)
        self.assertEqual(preimage(path, 10**16, 10**16, 10**18), (10000, 10000))
        for path in [(("+", True, False),), (("+", 0, False),), (("?", 2, False),), (("+", 2, 1),)]:
            with self.assertRaises(ValueError):
                preimage(path, 1, 5, 10)
        with self.assertRaises(ValueError):
            preimage((), 1, 5, True)
