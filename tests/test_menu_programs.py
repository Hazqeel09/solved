import unittest
from itertools import combinations

from checks.verify_root_sectors import replay
from solved.limits import ResourceLimit
from solved.menu_programs import shortest_from_menu


def exhaustive_minimum(menu, target):
    """Independent enumeration of every permitted increasing value sequence."""
    middle = tuple(sorted(set(menu) - {1, target}))
    if target == 1:
        return 0
    for cost in range(1, len(middle) + 2):
        for chosen in combinations(middle, cost - 1):
            row = (1, *chosen, target)
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
