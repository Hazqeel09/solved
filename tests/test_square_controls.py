import unittest
from itertools import combinations_with_replacement

from solved.chains import Chain, chains
from solved.square_controls import Description, encode, expand


class SquareControlTests(unittest.TestCase):
    def test_every_bounded_chain_roundtrip_and_square_inflation(self):
        count = 0
        for _, chain in chains(10**18, 2):
            description = encode(chain)
            reconstructed = expand(description)
            self.assertEqual(reconstructed.values, chain.values)
            self.assertEqual(description.length, len(chain.recipes))
            for i in range(len(description.runs)):
                inflated = list(description.runs)
                inflated[i] += 1
                higher = Description(description.control, tuple(inflated))
                result = expand(higher)
                self.assertEqual(higher.length, description.length + 1)
                self.assertLessEqual(result.values[-1], chain.values[-1] ** 2)
            count += 1
        self.assertGreater(count, 14000)

    def test_all_operand_aliases_in_small_chains(self):
        checked = 0
        for _, chain in chains(128, 3):
            for i, value in enumerate(chain.values[1:], 1):
                for a, b in combinations_with_replacement(range(i), 2):
                    for op, result in (
                        ("+", chain.values[a] + chain.values[b]),
                        ("*", chain.values[a] * chain.values[b]),
                    ):
                        if result != value:
                            continue
                        recipes = list(chain.recipes)
                        recipes[i - 1] = (op, a, b)
                        description = encode(Chain(chain.values, tuple(recipes)))
                        self.assertEqual(expand(description).values, chain.values)
                        for j in range(len(description.runs)):
                            lengths = list(description.runs)
                            lengths[j] += 1
                            inflated = expand(Description(description.control, tuple(lengths)))
                            self.assertLessEqual(inflated.values[-1], chain.values[-1] ** 2)
                        checked += 1
        self.assertGreater(checked, 1000)

    def test_saved_reads_and_multiple_excess_squares(self):
        chain = Chain(
            (1, 2, 4, 16, 256, 65536, 65552),
            (("+", 0, 0), ("*", 1, 1), ("*", 2, 2), ("*", 3, 3), ("*", 4, 4), ("+", 3, 5)),
        )
        encoded = encode(chain)
        self.assertEqual(encoded.runs, (2, 2))
        higher = Description(encoded.control, (3, 4))
        self.assertEqual(higher.length - encoded.length, 3)
        self.assertLessEqual(expand(higher).values[-1], chain.values[-1] ** 8)
        # Canonical squares include 2+2 at head 2, preserving the numerical trace.
        alternate = Chain((1, 2, 4), (("+", 0, 0), ("+", 1, 1)))
        self.assertEqual(expand(encode(alternate)).values, alternate.values)

    def test_negative_power_gap_for_every_pair_of_tower_indices(self):
        for k in range(2, 10):
            first = 1 << (1 << (k - 1))
            for gap in range(1, 5):
                self.assertGreater(first ** (1 << gap) - 1, (first - 1) ** (1 << gap))

    def test_input_contracts(self):
        for c in (
            Chain((), ()),
            Chain((1, 2), (("*", 0, 0),)),
            Chain((1, 1), (("*", 0, 0),)),
            Chain((1, 2), (("+", True, 0),)),
        ):
            with self.assertRaises(ValueError):
                encode(c)
        for d in (
            Description((("squares", 0, None),), (0,)),
            Description((("+", 1, 0),), ()),
            Description((), (1,)),
        ):
            with self.assertRaises(ValueError):
                expand(d)
