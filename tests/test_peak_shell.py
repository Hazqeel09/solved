import unittest
from itertools import product

from solved.peak_shell import first_visits, one_departure, total_bound


def oracle(seeds, depth, limit, max_nonsquares):
    states = {(frozenset(seeds), 0)}
    visits = dict.fromkeys(seeds, 0)
    for t in range(1, depth + 1):
        new = set()
        for bank, b in states:
            peak = max(bank)
            for x, y in product(bank, repeat=2):
                vs = [x + y, x * y, x - y]
                if x % y == 0:
                    vs.append(x // y)
                for v in vs:
                    cost = b + int(v != peak**2)
                    if 0 < v <= limit and cost <= max_nonsquares:
                        new.add((bank | {v}, cost))
                        visits.setdefault(v, t)
        states = new
    return visits


class ShellTests(unittest.TestCase):
    def test_exact_outer_shell_and_sound_times(self):
        for seeds in ((1,), (2,), (2, 2), (3,), (1, 3), (2, 3), (3, 7), (4, 6, 8)):
            cap = 42
            for depth in range(4):
                if max(seeds) >= 3:
                    self.assertEqual(
                        one_departure(seeds, depth, cap), set(oracle(seeds, depth, cap, 1))
                    )
            true = oracle(seeds, 4, cap, 4)
            bounds = first_visits(seeds, true, cap)
            self.assertTrue(all(bounds[v] <= t for v, t in true.items()), (seeds, true, bounds))

    def test_seed_activation_and_new_exclusion(self):
        self.assertEqual(first_visits((1,), (1,), 1), {1: 0})
        self.assertEqual(first_visits((2,), (1, 2), 2), {1: 1, 2: 0})
        self.assertEqual(first_visits((1,), (7,), 100), {7: 4})
        self.assertEqual(first_visits((2, 3), (19,), 100), {19: 3})
        self.assertEqual(total_bound({2: 0, 19: 3, 20: 3}), 4)
        self.assertEqual(total_bound({}), 0)

    def test_invalid(self):
        for seeds, targets, cap in [
            ((), (1,), 10),
            ((True,), (), 5),
            ((3,), (-1,), 5),
            ((2,), (), 1),
        ]:
            with self.assertRaises(ValueError):
                first_visits(seeds, targets, cap)
