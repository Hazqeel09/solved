import unittest
from itertools import product

from checks.verify_nonsquare_bound import below_power_of_two, census, check_chain, marked_evaluate
from solved.chains import Chain, chains
from solved.square_controls import Description, encode, expand


class NonsquareBoundTests(unittest.TestCase):
    def test_power_comparison_and_large_exponents(self):
        for n in range(200):
            for e in range(12):
                self.assertEqual(below_power_of_two(n, e), n <= 2**e)
        self.assertTrue(below_power_of_two(10**100, 10**100))
        for args in ((-1, 2), (2, -1), (True, 2), (2, 1.0)):
            with self.assertRaises(ValueError):
                below_power_of_two(*args)

    def test_envelope_and_control_bounds(self):
        result = census(10000, 3)
        self.assertEqual(sum(result["chains_by_defect"].values()), 45211)
        self.assertLessEqual(result["maximum_nonsquares_by_defect"][3], 16)
        self.assertEqual(check_chain(Chain((1,), ())), (0, 0))
        # 2+2 is a canonical square by value, despite the written addition.
        self.assertEqual(check_chain(Chain((1, 2, 4), (("+", 0, 0), ("+", 1, 1)))), (0, 1))
        with self.assertRaises(ValueError):
            check_chain(Chain((1, 2, 5), (("+", 0, 0), ("+", 0, 1))))

    def test_marked_interpreter_rejects_invalid_descriptions(self):
        for description in (
            Description((("-", 0, 0),), ()),
            Description((("+", True, 0),), ()),
            Description((("*", 1, 0),), ()),
            Description((("squares", 0, None),), ()),
            Description((("squares", 0, None),), (0,)),
            Description((("squares", 0, None),), (True,)),
            Description((), (1,)),
        ):
            with self.assertRaises(ValueError):
                marked_evaluate(description)

    def test_comparable_controls_preserve_the_exact_cost_difference(self):
        compared = 0
        for _, chain in chains(1000, 2):
            description = encode(chain)
            old, cost = marked_evaluate(description)
            self.assertEqual((old, cost), (chain.values[-1], len(chain.recipes)))
            for differences in product(range(2), repeat=len(description.runs)):
                lengths = tuple(a + b for a, b in zip(description.runs, differences))
                grown = Description(description.control, lengths)
                value, new_cost = marked_evaluate(grown)
                self.assertEqual(new_cost - cost, sum(differences))
                self.assertEqual(value, expand(grown).values[-1])
                self.assertLessEqual(value, old ** (1 << (new_cost - cost)))
                compared += 1
        self.assertGreater(compared, 1000)
