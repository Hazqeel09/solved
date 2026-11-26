import unittest

from checks.verify_root_sectors import replay, verify
from solved.chains import Chain, level
from solved.limits import ResourceLimit
from solved.menu_programs import shortest_from_menu
from solved.root_sectors import four_event_menu, reduce_square


def explicit_chain(values):
    """Independent all-pairs recipe search for short hand-written fixtures."""
    recipes = []
    for i, target in enumerate(values[1:], 1):
        candidates = [
            (op, a, b)
            for a in range(i)
            for b in range(a, i)
            for op, value in (("+", values[a] + values[b]), ("*", values[a] * values[b]))
            if value == target
        ]
        if not candidates:
            raise AssertionError("fixture is not an AM chain")
        recipes.append(candidates[0])
    return Chain(tuple(values), tuple(recipes))


class RootSectorTests(unittest.TestCase):
    def test_all_final_recipe_aliases_in_a_complete_finite_range(self):
        record = verify(8, aliases=True)
        self.assertGreater(record["checked_square_chains_or_recipe_variants"], 5000)
        self.assertEqual(
            set(record["rules"]),
            {
                "trailing_square",
                "halve_available_factors",
                "exceptional_sum",
                "unused_first_event",
                "exceptional_product",
                "paired_twos",
                "halve_first_product",
                "halve_two_products",
                "doubled_tower_sum",
                "seven_ray",
                "seven_square_base",
                "retained_root",
                "four_event_menu",
            },
        )

    def test_hand_written_boundary_cases_and_operand_orders(self):
        for values in (
            (1, 2, 4, 5, 9),
            (1, 2, 4, 16, 18, 36),
            (1, 2, 4, 16, 20, 36),
            (1, 2, 4, 16, 32, 64),
            (1, 2, 4, 5, 6, 36),
            (1, 2, 4, 16, 20, 400, 160000, 640000),
            (1, 2, 4, 16, 256, 1024, 4096),
        ):
            chain = explicit_chain(values)
            reversed_chain = Chain(chain.values, tuple((op, b, a) for op, a, b in chain.recipes))
            for source in (chain, reversed_chain):
                result = reduce_square(source)
                self.assertEqual(replay(result.chain) ** 2, values[-1])
                self.assertGreaterEqual(result.saved_instructions, 1)
                self.assertLessEqual(len(result.chain.recipes) - level(result.root), 2)

    def test_long_square_runs_and_missing_first_product_root(self):
        for gap in (2, 3, 12):
            values = [1, 2, 4, 16, 64]
            recipes = [("+", 0, 0), ("*", 1, 1), ("*", 2, 2), ("*", 2, 3)]
            for _ in range(gap):
                recipes.append(("*", len(values) - 1, len(values) - 1))
                values.append(values[-1] ** 2)
            recipes.append(("*", 4, len(values) - 1))
            values.append(64 * values[-1])
            source = Chain(tuple(values), tuple(recipes))
            result = reduce_square(source)
            self.assertEqual(result.rule, "halve_first_product")
            self.assertEqual(result.saved_instructions, 1)
            self.assertEqual(replay(result.chain) ** 2, values[-1])

    def test_unsupported_inputs_are_not_reported_as_root_obstructions(self):
        for source in (
            explicit_chain((1, 2, 4)),
            explicit_chain((1, 2, 4, 5, 6)),
            explicit_chain((1, 2, 3, 4, 7, 49, 2401, 117649)),
            Chain((1, 2, 4, 5, 9), (("+", 0, 0), ("*", 1, 1), ("+", 0, 2), ("+", 4, 4))),
            Chain((1, 2), (("+", True, 0),)),
            None,
        ):
            with self.assertRaises(ValueError):
                reduce_square(source)
        with self.assertRaises(ValueError):
            verify(True)

    def test_source_lists_are_frozen(self):
        source = explicit_chain((1, 2, 4, 5, 9))
        values, recipes = list(source.values), [list(r) for r in source.recipes]
        result = reduce_square(Chain(values, recipes))
        values[-1] = 100
        recipes[-1][0] = "*"
        self.assertEqual(result.chain.values, (1, 2, 3))
        self.assertEqual(result.root, 3)

    def test_four_event_shared_helpers_outside_source_and_roots(self):
        source = explicit_chain((1, 2, 4, 16, 64, 80, 6400, 409600))
        menu = four_event_menu(source)
        self.assertIn(20, menu)
        self.assertIn(32, menu)
        result = reduce_square(source)
        self.assertEqual(result.chain.values, (1, 2, 4, 16, 20, 32, 640))
        self.assertEqual(result.saved_instructions, 1)
        for kwargs in ({"max_states": 0}, {"max_pairs": 0}):
            with self.assertRaises(ResourceLimit):
                reduce_square(source, **kwargs)
        with self.assertRaises(ValueError):
            four_event_menu(explicit_chain((1, 2, 4, 5, 9)))
        with self.assertRaises(ValueError):
            reduce_square(source, max_states=True)

    def test_parameterized_exchange_family_and_restricted_menu_gap(self):
        from math import isqrt

        for j in range(9):
            values = [1, 2]
            for _ in range(j + 2):
                values.append(values[-1] ** 2)
            A, u = values[-1], values[-2]
            B = A * u
            C = B + A
            values.extend((B, C, C * C, C * C * B))
            source = explicit_chain(values)
            root = isqrt(values[-1])
            bare = set(values) | {isqrt(v) for v in values if isqrt(v) ** 2 == v}
            bare = tuple(sorted(v for v in bare if v <= root))
            self.assertIsNone(shortest_from_menu(bare, root, j + 6))
            restricted = shortest_from_menu(bare, root, j + 7)
            self.assertEqual(len(restricted.recipes), j + 7)
            result = reduce_square(source)
            self.assertEqual(replay(result.chain), root)
            self.assertEqual(len(result.chain.recipes), j + 6)
