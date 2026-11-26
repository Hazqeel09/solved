import unittest
from itertools import combinations

from solved.chains import chains, level
from solved.counting import charged_steps, coordinates, family_size_at_level, lower_witness
from solved.seven_steps import low_defect


class CountingTests(unittest.TestCase):
    def test_inverse_uniqueness_and_count_by_level(self):
        for lev in range(4, 13):
            seen = set()
            for k in range(2, lev - 1):
                for j, i in combinations(range(k), 2):
                    for h in range(1, lev - k):
                        d = lev - k - 1 - h
                        seq = lower_witness(k, i, j, h, d)
                        n = seq[-1]
                        self.assertNotIn(n, seen)
                        seen.add(n)
                        self.assertEqual((level(n), len(seq) - 1, low_defect(n)), (lev, lev + 2, 2))
                        self.assertEqual(coordinates(n), (k, i, j, h, d))
            self.assertEqual(len(seen), family_size_at_level(lev))

    def test_complete_numerical_sequences_and_four_charges(self):
        for defect, chain in chains(10**18):
            self.assertLessEqual(sum(charged_steps(chain.values, chain.recipes)), 4)
            if coordinates(chain.values[-1]) is not None:
                self.assertEqual(low_defect(chain.values[-1]), 2)
        for bad in (True, 0, -1):
            with self.assertRaises(ValueError):
                coordinates(bad)
        for n in (1, 2, 3, 16, 17):
            self.assertIsNone(coordinates(n))
        with self.assertRaises(ValueError):
            lower_witness(2, 1, 0, 0)
        with self.assertRaises(ValueError):
            charged_steps((1, 3), (("+", 0, 0),))
