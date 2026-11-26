import unittest
from fractions import Fraction
from itertools import product

from checks.classical import (
    expanded_lower_bound,
    mersenne_chain,
    periodic_density,
    shortest_chain,
)


class ClassicalTests(unittest.TestCase):
    def test_small_periods(self):
        for q in range(1, 9):
            for bits in product((False, True), repeat=q):
                before = periodic_density(bits)
                after = expanded_lower_bound(bits)
                if 0 < before < 1:
                    self.assertGreater(after, before)
                hist = sorted({n for n in range(1, 5 * q + 1) if bits[(n - 1) % q]})
                number_set = {0, *hist}
                enlarged = number_set | {n + 1 for n in number_set}
                direct = [
                    Fraction(len(enlarged.intersection(range(1, n + 1))), n)
                    for n in range(1, 5 * q + 1)
                ]
                mean = Fraction(sum(v or bits[i - 1] for i, v in enumerate(bits)), q)
                self.assertEqual(after, min(*direct, mean))

    def test_finite_constructions(self):
        self.assertEqual(
            [len(shortest_chain(i)) - 1 for i in range(1, 11)],
            [0, 1, 2, 2, 3, 3, 4, 3, 4, 4],
        )
        self.assertEqual(mersenne_chain([1, 2, 3]), [1, 2, 3, 6, 7])
        self.assertEqual(shortest_chain(255, product=True)[-1], 255)
        with self.assertRaises(ValueError):
            mersenne_chain([1, 4])
        with self.assertRaises(ValueError):
            periodic_density([])
