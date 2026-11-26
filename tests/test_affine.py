import itertools
import unittest

from solved.affine import balanced_domain
from solved.cycles import Edge, solve


class AffineTests(unittest.TestCase):
    def test_arithmetic_progressions_match_replayed_full_domain(self):
        cap = 19
        paths = (
            (),
            (("/", 2, False),),
            (("-", 18, True), ("/", 3, False)),
            (("+", 3, False), ("/", 6, False)),
            (("*", 3, True), ("-", 5, False)),
        )
        for t, op, p, q in itertools.product((2, 3, 9, 17), "+-/", paths, paths):
            edges = (Edge(4, 5, op, t, p, q),) * 2
            domain = balanced_domain(edges, {2, 3, 5, 6, 18}, cap)
            vertices = solve(edges, {2, 3, 5, 6, 18}, cap, root_domain=set(range(1, cap + 1)))
            self.assertEqual(list(domain), [r[0] for r in vertices.assignments])

    def test_non_coprime_guards_and_large_cap(self):
        cap = 10**18
        edges = (
            Edge(0, 1, "-", 1, (("/", 6, False),)),
            Edge(0, 2, "-", 1, (("/", 4, False),)),
        )
        domain = balanced_domain(edges, {4, 6}, cap)
        self.assertEqual((domain[0], domain.step, domain[-1]), (12, 12, cap - cap % 12))
        impossible = edges + (Edge(0, 3, "+", 9, (("+", 1, False), ("/", 2, False))),)
        self.assertEqual(list(balanced_domain(impossible, {1, 2, 4, 6}, cap)), [])
        self.assertIsNone(balanced_domain((Edge(0, 0, "*", 4),), (), cap))
        self.assertIsNone(balanced_domain((Edge(0, 1, "*", 4),), (), cap))

    def test_partial_domain_lost_by_symbolic_cancellation(self):
        edges = (Edge(0, 1, "+", 11, (("/", 2, True), ("/", 2, True))),)
        self.assertIsNone(balanced_domain(edges, {2}, 20))
