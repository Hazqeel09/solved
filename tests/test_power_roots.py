import unittest

from checks.classical import shortest_chain
from checks.verify_root_sectors import replay
from solved.chains import Chain, chains, level
from solved.limits import ResourceLimit
from solved.power_roots import (
    binary_exponents,
    lift_binary_powers,
    low_step_addition_chain,
    reduce_power_square,
)
from solved.root_sectors import reduce_square


def addition_chain(values):
    """Independent recipe recovery for numerical addition-only witnesses."""
    rows = []
    for i, value in enumerate(values[1:], 1):
        a, b = next((a, b) for a in range(i) for b in range(a, i) if values[a] + values[b] == value)
        rows.append(("+", a, b))
    return Chain(tuple(values), tuple(rows))


class PowerRootTests(unittest.TestCase):
    def test_classification_against_existing_unrestricted_exact_search(self):
        for n in range(1, 300):
            exact = shortest_chain(n)
            output = low_step_addition_chain(n)
            expected = len(exact) - 1 <= n.bit_length() + 1
            self.assertEqual(output is not None, expected, n)
            if output is not None:
                self.assertEqual(replay(output), n)
                self.assertEqual(len(output.values), len(exact), n)
                self.assertTrue(all(op == "+" for op, _, _ in output.recipes))
                self.assertLessEqual(
                    sum(y != 2 * x for x, y in zip(output.values, output.values[1:])), 3
                )

    def test_all_parameterized_families_and_halving(self):
        cases = set()
        for a in (0, 1, 7, 29):
            cases.add(135 << a)
            for d in (1, 2, 11):
                for e in (d + 1, d + 3, d + 19):
                    cases.update(
                        (
                            (1 + (1 << d) + (1 << e)) << a,
                            (3 + (9 << e)) << a,
                            ((1 + (1 << d)) * (1 + (1 << e))) << a,
                            (1 + (1 << d) + (1 << e) + (1 << (d + e + 1))) << a,
                        )
                    )
        for n in cases:
            result = low_step_addition_chain(n)
            self.assertIsNotNone(result, n)
            self.assertEqual(replay(result), n)
            self.assertEqual(len(result.recipes), n.bit_length() + 1)
            if n % 2 == 0:
                half = low_step_addition_chain(n // 2)
                self.assertIsNotNone(half)
                self.assertEqual(replay(half), n // 2)
                self.assertEqual(len(half.recipes) + 1, len(result.recipes))

    def test_conversion_charges_initial_write_and_preserves_references(self):
        for n in (1, 2, 7, 15, 23, 39, 135, 270, 511):
            original = addition_chain(shortest_chain(n))
            lifted = lift_binary_powers(original, max_bits=n + 1)
            self.assertEqual(replay(lifted), 1 << n)
            self.assertEqual(len(lifted.recipes), len(original.recipes) + 1)
            returned = binary_exponents(lifted)
            self.assertEqual(returned.values, original.values)
            self.assertEqual(replay(returned), n)
        # Doubling a value is an exponent increment, not an exponent doubling.
        source = Chain((1, 2, 4, 8, 16), (("+", 0, 0), ("+", 1, 1), ("+", 2, 2), ("*", 2, 2)))
        exponents = binary_exponents(source)
        self.assertEqual(exponents.values, (1, 2, 3, 4))
        self.assertEqual(replay(exponents), 4)
        self.assertEqual(replay(reduce_power_square(source)), 4)

    def test_exponent_construction_for_four_nontrivial_event_orders(self):
        # Exact exponent witnesses for GSG, GSGG, SGG and SGGG, respectively.
        for exponents in (
            (1, 2, 3, 4, 5, 8),
            (1, 2, 3, 4, 6, 10, 16),
            (1, 2, 3, 6, 7, 9, 16),
            (1, 2, 3, 6, 7, 13, 19, 32),
        ):
            source = lift_binary_powers(addition_chain(exponents), max_bits=exponents[-1] + 1)
            self.assertEqual(len(source.recipes) - level(source.values[-1]), 2)
            result = reduce_square(source, max_states=0, max_pairs=0)
            self.assertEqual(result.rule, "power_exponents")
            self.assertEqual(replay(result.chain) ** 2, source.values[-1])
            self.assertGreaterEqual(result.saved_instructions, 1)
            self.assertLessEqual(
                sum(y != x * x for x, y in zip(result.chain.values, result.chain.values[1:])), 4
            )
        for n in (2, 6, 14, 30, 78, 270):
            source = lift_binary_powers(low_step_addition_chain(n), max_bits=n + 1)
            root = reduce_power_square(source)
            self.assertEqual(replay(root), 1 << (n // 2))
            self.assertEqual(len(source.recipes), len(root.recipes) + 1)

    def test_normal_form_for_independently_enumerated_histories(self):
        checked, normal_forms = 0, {}
        for _, source in chains((1 << 64) - 1, 2):
            if len(source.values) == 1 or any(v & (v - 1) for v in source.values):
                continue
            exponent = binary_exponents(source).values[-1]
            if exponent not in normal_forms:
                ordinary = low_step_addition_chain(exponent)
                self.assertIsNotNone(ordinary)
                normal_forms[exponent] = lift_binary_powers(ordinary, max_bits=exponent + 1)
            normal = normal_forms[exponent]
            self.assertEqual(replay(normal), source.values[-1])
            self.assertLessEqual(len(normal.recipes), len(source.recipes))
            self.assertLessEqual(
                sum(y != x * x for x, y in zip(normal.values, normal.values[1:])), 4
            )
            checked += 1
        self.assertGreater(checked, 100)

    def test_malformed_inputs_and_output_size_budget(self):
        for target in (0, -1, True, 3.0, "7"):
            with self.assertRaises(ValueError):
                low_step_addition_chain(target)
        self.assertIsNone(low_step_addition_chain(191))
        for source in (
            None,
            Chain((1,), ()),
            addition_chain((1, 2, 3)),
            Chain((1, 2, 4), (("+", 0, 0), ("*", 3, 3))),
        ):
            with self.assertRaises(ValueError):
                binary_exponents(source)
        for source in (
            lift_binary_powers(addition_chain((1, 2, 3)), max_bits=4),
            lift_binary_powers(addition_chain((1, 2, 3, 4, 5, 6, 12)), max_bits=13),
        ):
            with self.assertRaises(ValueError):
                reduce_power_square(source)
        with self.assertRaises(ValueError):
            lift_binary_powers(Chain((1, 2, 4), (("+", 0, 0), ("*", 1, 1))), max_bits=5)
        for budget in (True, 0, -1, None, 3.0):
            with self.assertRaises(ValueError):
                lift_binary_powers(addition_chain((1, 2)), max_bits=budget)
        with self.assertRaises(ResourceLimit):
            lift_binary_powers(addition_chain((1, 2)), max_bits=2)
        huge = low_step_addition_chain(1 << 80)
        with self.assertRaises(ResourceLimit):
            lift_binary_powers(huge, max_bits=1_000_000)

    def test_input_lists_are_not_aliased(self):
        values, recipes = [1, 2, 3, 6], [["+", 0, 0], ["+", 0, 1], ["+", 2, 2]]
        lifted = lift_binary_powers(Chain(values, recipes), max_bits=7)
        values[-1] = 100
        recipes[-1][0] = "*"
        self.assertEqual(lifted.values, (1, 2, 4, 8, 64))
        self.assertEqual(replay(lifted), 64)
