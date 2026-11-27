import unittest
from math import isqrt

from test_root_sectors import explicit_chain

from checks.verify_root_retention import ALTERNATIVE, CONTROL, SOURCE, verify
from checks.verify_root_sectors import replay
from solved.chains import level
from solved.menu_programs import shortest_from_menu
from solved.root_sectors import four_event_menu


class RootRetentionTests(unittest.TestCase):
    def test_exact_counterexample_and_independent_census(self):
        record = verify()
        self.assertEqual(record["joint_minimum"], 7)
        self.assertEqual(record["independent_census_sequences"], 1548)
        self.assertEqual(len(record["all_six_write_root_histories"]), 2)
        self.assertEqual([r["minimum"] for r in record["endpoint_minima"]], [6, 7])
        roots = {isqrt(v) for v in SOURCE if isqrt(v) ** 2 == v}
        self.assertEqual(roots, {1, 2, 10, 2000})
        self.assertLessEqual(roots, set(record["joint_witness"]))

    def test_equally_short_histories_have_different_retention_requirements(self):
        self.assertEqual(SOURCE[-1], ALTERNATIVE[-1])
        self.assertEqual(len(SOURCE), len(ALTERNATIVE))
        self.assertEqual(len(SOURCE) - 1 - level(SOURCE[-1]), 2)
        required = {isqrt(v) for v in ALTERNATIVE if isqrt(v) ** 2 == v}
        self.assertLessEqual(required, set(ALTERNATIVE[:-1]))
        self.assertEqual(replay(explicit_chain(ALTERNATIVE[:-1])), 2000)
        self.assertNotIn(10, ALTERNATIVE[:-1])

    def test_menu_failure_is_not_a_global_obstruction(self):
        source = explicit_chain((1, 2, 4, 16, 64, 80, 6400, 409600))
        menu = four_event_menu(source)
        self.assertNotIn(10, menu)
        self.assertIsNone(shortest_from_menu(menu, 640, 6, required=(8, 80)))
        result = shortest_from_menu((*menu, 10), 640, 6, required=(8, 80))
        self.assertEqual(replay(result), 640)
        self.assertEqual(len(result.recipes), 6)
        self.assertEqual(replay(explicit_chain(CONTROL)), 640)
        self.assertLessEqual({8, 80, 640}, set(CONTROL))
