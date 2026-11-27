import unittest
from itertools import combinations

from checks.verify_root_sectors import replay
from solved.limits import ResourceLimit
from solved.menu_programs import shortest_from_menu


def exhaustive_minimum(menu, target, required=()):
    """Independent enumeration of every permitted increasing value sequence."""
    middle = tuple(sorted(set(menu) - {1, target}))
    if target == 1:
        return 0
    for cost in range(1, len(middle) + 2):
        for chosen in combinations(middle, cost - 1):
            row = (1, *chosen, target)
            if not set(required) <= set(row):
                continue
            if all(
                any(
                    value == row[a] + row[b] or value == row[a] * row[b]
                    for a in range(i)
                    for b in range(a, i)
                )
                for i, value in enumerate(row[1:], 1)
            ):
                return cost
    return None


class MenuProgramTests(unittest.TestCase):
    def test_every_small_menu_against_value_sequence_enumeration(self):
        for target in range(2, 10):
            interior = tuple(range(2, target))
            for mask in range(1 << len(interior)):
                menu = (1, *(v for i, v in enumerate(interior) if mask & (1 << i)), target)
                optimum = exhaustive_minimum(menu, target)
                for budget in (0, 2, 4, 8):
                    result = shortest_from_menu(menu, target, budget)
                    if optimum is None or optimum > budget:
                        self.assertIsNone(result)
                    else:
                        self.assertEqual(replay(result), target)
                        self.assertEqual(len(result.recipes), optimum)
                        self.assertTrue(set(result.values) <= set(menu))

    def test_incomparable_equal_cost_supports_and_shared_ancestors(self):
        for target in (15, 20):
            result = shortest_from_menu((1, 2, 3, 4, 5, target), target, 4)
            self.assertEqual(len(result.recipes), 4)
            self.assertEqual(replay(result), target)
        result = shortest_from_menu((1, 2, 4, 5, 16, 80), 80, 5)
        self.assertEqual(len(result.recipes), 5)
        self.assertEqual(replay(result), 80)

    def test_every_small_menu_and_joint_requirement_against_enumeration(self):
        for target in range(2, 10):
            interior = tuple(range(2, target))
            for mask in range(1 << len(interior)):
                middle = tuple(v for i, v in enumerate(interior) if mask & (1 << i))
                menu = (1, *middle, target)
                for required_mask in range(1 << len(middle)):
                    required = tuple(v for i, v in enumerate(middle) if required_mask & (1 << i))
                    optimum = exhaustive_minimum(menu, target, required)
                    for budget in (0, 2, 4, 8):
                        result = shortest_from_menu(menu, target, budget, required=required)
                        if optimum is None or optimum > budget:
                            self.assertIsNone(result)
                        else:
                            self.assertEqual(replay(result), target)
                            self.assertEqual(len(result.recipes), optimum)
                            self.assertTrue(set(required) <= set(result.values) <= set(menu))

    def test_joint_supports_need_incomparable_individual_solutions(self):
        menu = (1, 2, 3, 4, 5, 16)
        first = shortest_from_menu(menu, 5, 3)
        second = shortest_from_menu(menu, 16, 3)
        self.assertEqual(len(set(first.values) | set(second.values)) - 1, 5)
        result = shortest_from_menu(menu, 16, 4, required=(5,))
        self.assertEqual(result.values, (1, 2, 4, 5, 16))
        self.assertIsNone(shortest_from_menu(menu, 16, 3, required=(5,)))

    def test_joint_limits_are_charged_and_do_not_mean_infeasible(self):
        menu = (1, 2, 3, 4)
        self.assertEqual(shortest_from_menu(menu, 4, 3, max_states=3).values, (1, 2, 4))
        self.assertEqual(shortest_from_menu(menu, 4, 3, max_pairs=5).values, (1, 2, 4))
        for limits in ({"max_states": 3}, {"max_pairs": 5}):
            with self.assertRaises(ResourceLimit):
                shortest_from_menu(menu, 4, 3, required=(3,), **limits)
        result = shortest_from_menu(menu, 4, 3, required=(3,), max_states=None, max_pairs=None)
        self.assertEqual(result.values, (1, 2, 3, 4))

    def test_joint_contract_validation_and_unreachable_requirement(self):
        for required in ((True,), (0,), (5,), (3.0,), ("3",)):
            with self.assertRaises(ValueError):
                shortest_from_menu((1, 2, 3, 4, 5), 4, 3, required=required)
        with self.assertRaises(ValueError):
            shortest_from_menu((1, 2, 4), 4, 3, required=(3,))
        self.assertIsNone(shortest_from_menu((1, 2, 4, 7, 8), 8, 10, required=(7,)))
        required = [1, 3, 3, 4]
        result = shortest_from_menu((1, 2, 3, 4), 4, 3, required=iter(required))
        required[:] = [999]
        self.assertEqual(result.values, (1, 2, 3, 4))
        self.assertEqual(shortest_from_menu((1, 2), 1, 0, required=(1,)).values, (1,))

    def test_limits_and_exhaustion_have_different_meanings(self):
        self.assertIsNone(shortest_from_menu((1, 3), 3, 20))
        self.assertIsNone(shortest_from_menu((1, 2), 2, 0))
        for kwargs in ({"max_states": 0}, {"max_pairs": 0}):
            with self.assertRaises(ResourceLimit):
                shortest_from_menu((1, 2), 2, 1, **kwargs)
        self.assertEqual(shortest_from_menu((1, 2), 1, 0, max_states=0, max_pairs=0).values, (1,))
        self.assertEqual(
            shortest_from_menu((1, 2, 4), 4, 2, max_states=None, max_pairs=None).values,
            (1, 2, 4),
        )

    def test_contracts_duplicates_iterators_and_unused_overshoots(self):
        for menu, target, budget in (
            ((1, True, 2), 2, 1),
            ((1, 0, 2), 2, 1),
            ((2,), 2, 1),
            ((1, 2), 3, 2),
            ((1, 2), True, 2),
            ((1, 2), 2, -1),
        ):
            with self.assertRaises(ValueError):
                shortest_from_menu(menu, target, budget)
        for kwargs in ({"max_states": -1}, {"max_pairs": True}):
            with self.assertRaises(ValueError):
                shortest_from_menu((1, 2), 2, 1, **kwargs)
        result = shortest_from_menu(iter((16, 4, 1, 2, 2, 100)), 16, 3)
        self.assertEqual(result.values, (1, 2, 4, 16))
