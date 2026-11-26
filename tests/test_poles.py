import itertools
import unittest

from solved.cycles import Edge, solve
from solved.poles import common_poles, inherited_factors, nonlinear_domain


class NonlinearTests(unittest.TestCase):
    def test_same_pole_gcd_and_large_guard(self):
        cap = 10**18
        es = (Edge(0, 1, "*", 60), Edge(0, 2, "*", 84))
        cover = nonlinear_domain(es, (), cap)
        self.assertEqual(cover.poles, ((1, 0, 12),))
        self.assertEqual(cover.roots, (1, 2, 3, 4, 6, 12))
        self.assertIsNone(nonlinear_domain(es, (), cap, 0).roots)
        self.assertEqual(inherited_factors(2**120 * 3**22, (6,)), {2: 120, 3: 22})
        self.assertEqual(common_poles([(2, 1, -3, 6), (0, 7, 2, -4)]), {(1, -2): 1})
        self.assertIsNone(nonlinear_domain((Edge(0, 0, "*", 9),), (), cap))

    def test_differential_roots_including_poles_and_illegal_prefixes(self):
        paths = (
            (),
            (("/", 6, True),),
            (("-", 7, True), ("/", 6, True)),
            (("/", 2, True), ("/", 2, True)),
            (("*", 3, False), ("/", 2, False)),
        )
        for op, target, path, q in itertools.product("+-*/", (1, 3, 8), paths, paths):
            es = (Edge(0, 1, op, target, path, q),) * 2
            cover = nonlinear_domain(es, (2, 3, 6, 7), 21)
            if cover is None:
                continue
            oracle = solve(es, (2, 3, 6, 7), 21, root_domain=range(1, 22))
            self.assertEqual(cover.roots, tuple(r[0] for r in oracle.assignments))
