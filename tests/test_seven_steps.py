import unittest
from itertools import combinations_with_replacement
from math import isqrt

from solved.chains import catalogue as bounded
from solved.chains import chains, level
from solved.seven_steps import (
    catalogue,
    extreme,
    low_defect,
    signature_envelope,
    six_step_witness,
)


class SevenStepTests(unittest.TestCase):
    def test_full_bounded_population_and_each_unbounded_base(self):
        rows = catalogue()["squaring_rays"]
        self.assertEqual(len(rows), 12)
        self.assertEqual(sum(r["minimum_defect_on_entire_ray"] == 2 for r in rows), 8)
        winners = set()
        one = bounded(max(r["base"] for r in rows), 1)[0]
        for row in rows:
            path = row["witness"]
            n = row["base"]
            for j, v in enumerate(path[1:], 1):
                self.assertTrue(
                    any(v in (a + b, a * b) for a, b in combinations_with_replacement(path[:j], 2))
                )
            self.assertEqual(path[-1], n)
            self.assertEqual(len(path) - 1 - level(n), 2)
            self.assertEqual(sum(b != a * a for a, b in zip(path, path[1:])), 7)
            self.assertEqual(
                row["minimum_defect_on_entire_ray"],
                len(one[n].recipes) - level(n) if n in one else 2,
            )
            for _ in range(6):
                self.assertEqual(low_defect(n), row["minimum_defect_on_entire_ray"])
                if n <= 10**18:
                    winners.add(n)
                n = n * n
        observed = {
            c.values[-1]
            for d, c in chains(10**18)
            if d == 2 and sum(b != a * a for a, b in zip(c.values, c.values[1:])) == 7
        }
        self.assertEqual(winners, observed)

    def test_second_best_against_complete_next_choices(self):
        for _, c in chains(300):
            row = c.values
            if len(row) < 3:
                continue
            m = row[-1]
            opts = sorted(
                {
                    v
                    for a, b in combinations_with_replacement(row, 2)
                    for v in (a + b, a * b)
                    if m < v < m * m
                }
            )
            self.assertEqual(opts[-2:], [extreme(row, True), extreme(row, False)])

    def test_gap_clipping_against_uncapped_exact_arithmetic(self):
        for initial in (3, 4):
            for gaps in ((3, 0, 0, 0, 0), (0, 4, 1, 0, 0), (1, 2, 0, 3, 1), (0, 0, 0, 0, 3)):
                for ds in ((), (0,), (3,), (1, 4)):
                    vals = [1, 2, initial]
                    for j, g in enumerate(gaps):
                        for _ in range(g):
                            vals.append(vals[-1] ** 2)
                        vals.append(extreme(vals, j in ds))
                    ref = len(vals) - 1 - level(vals[-1]) <= 2
                    self.assertEqual(signature_envelope(initial, gaps, ds) is not None, ref)

    def test_unbounded_six_step_obstruction_on_representatives(self):
        old_max = 0
        for h in range(3, 13):
            roots = []
            for r in (0, *(1 << j for j in range(h))):
                seq = six_step_witness(h, r)
                n = seq[-1]
                roots.append(n)
                self.assertEqual(n.bit_count(), 10)
                self.assertNotEqual(isqrt(n) ** 2, n)
                self.assertEqual(low_defect(n), 2)
                self.assertEqual(len(seq) - 1 - level(n), 2)
                self.assertEqual(sum(b != a * a for a, b in zip(seq, seq[1:])), 6)
                for j, x in enumerate(seq[1:], 1):
                    self.assertTrue(
                        any(
                            x == a + b or x == a * b
                            for a, b in combinations_with_replacement(seq[:j], 2)
                        )
                    )
            self.assertTrue(old_max < min(roots))
            self.assertEqual(len(set(roots)), h + 1)
            old_max = max(roots)
        with self.assertRaises(ValueError):
            six_step_witness(3, 3)

    def test_published_low_class_and_root_closure(self):
        one = bounded(100000, 1)[0]
        for n in range(1, 100001):
            delta = low_defect(n)
            self.assertEqual(delta, len(one[n].recipes) - level(n) if n in one else 2)
            self.assertEqual(low_defect(n * n), delta)
        for n in (True, 0, -1):
            with self.assertRaises(ValueError):
                low_defect(n)
