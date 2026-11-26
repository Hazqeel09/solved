import random
import unittest
from itertools import product

from solved.monotone_recovery import Observation, Polynomial, recover
from solved.product_intervals import recover as old_recover


def exact(poly, x, y):
    return sum(c * x**p * y**q for c, p, q in poly.terms)


def oracle(domains, edges):
    return [
        row
        for row in product(*(range(a, b + 1) for a, b in domains))
        if all(e.lower <= exact(e.polynomial, row[e.left], row[e.right]) <= e.upper for e in edges)
    ]


class MonotoneRecoveryTests(unittest.TestCase):
    def test_capped_values_and_increments_are_exact(self):
        rng = random.Random(113027)
        for _ in range(1200):
            poly = Polynomial(
                tuple((rng.randrange(6), rng.randrange(9), rng.randrange(9)) for _ in range(4))
            )
            x, y, cap = rng.randrange(1, 9), rng.randrange(1, 9), rng.randrange(1, 10000)
            value = exact(poly, x, y)
            self.assertEqual(poly.evaluate(x, y, cap), min(value, cap))
            dx, dy = exact(poly, x + 1, y) - value, exact(poly, x, y + 1) - value
            self.assertEqual(poly.increments(x, y, cap), (min(dx, cap), min(dy, cap)))
        poly = Polynomial(((1, 10**100, 0),))
        self.assertEqual(poly.evaluate(1, 3, 1000), 1)
        self.assertEqual(poly.evaluate(2, 3, 1000), 1000)
        self.assertEqual(poly.increments(1, 3, 1000), (1000, 0))

    def test_against_exhaustive_assignments_and_edge_reversal(self):
        rng = random.Random(271126)
        statuses = {"unique": 0, "infeasible": 0, "undetermined": 0}
        for n in range(1, 5):
            for _ in range(200):
                domains = []
                for i in range(n):
                    lo = rng.randrange(1, 5)
                    domains.append((lo, lo + rng.randrange(3)))
                truth = [rng.randint(a, b) for a, b in domains]
                edges = []
                for _ in range(rng.randrange(1, 7)):
                    u, v = rng.randrange(n), rng.randrange(n)
                    poly = Polynomial(
                        tuple(
                            (rng.randrange(4), rng.randrange(4), rng.randrange(4)) for _ in range(3)
                        )
                    )
                    target = exact(poly, truth[u], truth[v])
                    lower = max(0, target + rng.randrange(-3, 4))
                    edges.append(Observation(u, v, poly, lower, lower + rng.randrange(6)))
                possible = oracle(domains, edges)
                result = recover(iter(domains), iter(edges))
                statuses[result.status] += 1
                if result.status == "unique":
                    self.assertEqual(possible, [result.values])
                elif result.status == "infeasible":
                    self.assertEqual(possible, [])
                for row in possible:
                    for v, value in result.forced:
                        self.assertEqual(row[v], value)
                reversed_edges = [
                    Observation(
                        e.right,
                        e.left,
                        Polynomial(tuple((c, q, p) for c, p, q in e.polynomial.terms)),
                        e.lower,
                        e.upper,
                    )
                    for e in edges
                ]
                reversed_result = recover(domains, reversed_edges)
                self.assertEqual(
                    (reversed_result.status, reversed_result.values), (result.status, result.values)
                )
                for root, walk in result.walks:
                    vertex = root
                    self.assertEqual(len(walk) % 2, 1)
                    for arc_id in walk:
                        arc = result.arcs[arc_id]
                        self.assertEqual(arc.source, vertex)
                        vertex = arc.destination
                    self.assertEqual(vertex, root)
        self.assertTrue(all(count > 50 for count in statuses.values()), statuses)

    def test_one_way_triangle_and_small_factor_leaf(self):
        linear = Polynomial(((1, 1, 0), (100, 0, 1)))
        values = (5, 7, 11)
        edges = [
            Observation(
                i,
                (i + 1) % 3,
                linear,
                values[i] + 100 * values[(i + 1) % 3] - 1,
                values[i] + 100 * values[(i + 1) % 3] + 1,
            )
            for i in range(3)
        ]
        result = recover([(1, 100)] * 3, edges)
        self.assertEqual(result.values, values)
        self.assertEqual(len(result.arcs), 3)
        self.assertEqual({(a.source, a.destination) for a in result.arcs}, {(0, 1), (1, 2), (2, 0)})
        domains = [(100, 1000)] * 3 + [(1, 9)]
        values = (101, 107, 109, 3)
        raw = [
            (u, v, values[u] * values[v] - 1, values[u] * values[v] + 1)
            for u, v in ((0, 1), (1, 2), (2, 0), (2, 3))
        ]
        with self.assertRaises(ValueError):
            old_recover(domains, raw)
        poly = Polynomial(((1, 1, 1),))
        self.assertEqual(
            recover(
                domains, [Observation(u, v, poly, lower, upper) for u, v, lower, upper in raw]
            ).values,
            values,
        )

    def test_nonlinear_large_domains_loops_and_independent_components(self):
        poly = Polynomial(((1, 2, 0), (1, 0, 2)))
        truth = (10**10 + 7, 10**11 + 9, 10**12 + 39)
        edges = [
            Observation(
                i,
                (i + 1) % 3,
                poly,
                truth[i] ** 2 + truth[(i + 1) % 3] ** 2 - 100,
                truth[i] ** 2 + truth[(i + 1) % 3] ** 2 + 100,
            )
            for i in range(3)
        ]
        result = recover([(1000, 10**18)] * 3, edges)
        self.assertEqual(result.values, truth)
        self.assertLess(result.evaluations, 15000)
        product_poly = Polynomial(((1, 1, 1),))
        self.assertEqual(
            recover([(10, 12)], [Observation(0, 0, product_poly, 121, 121)]).values, (11,)
        )
        self.assertEqual(
            recover([(10, 12)], [Observation(0, 0, product_poly, 110, 110)]).status, "infeasible"
        )
        self.assertEqual(
            recover([(10, 12), (7, 7)], [Observation(0, 0, product_poly, 121, 121)]).values, (11, 7)
        )
        self.assertEqual(
            recover([(10, 12), (7, 8)], [Observation(0, 0, product_poly, 121, 121)]).status,
            "undetermined",
        )

    def test_affine_inversion_avoids_domain_binary_search(self):
        values = (10**12 + 39, 10**13 + 7, 10**11 + 11, 10**12 + 333, 10**13 + 141)
        poly = Polynomial(((1, 1, 1),))
        edges = [
            Observation(
                i,
                (i + 1) % 5,
                poly,
                values[i] * values[(i + 1) % 5] - 10000,
                values[i] * values[(i + 1) % 5] + 9999,
            )
            for i in range(5)
        ]
        result = recover([(20000, 10**18)] * 5, edges)
        self.assertEqual(result.values, values)
        self.assertLessEqual(result.evaluations, 400)

    def test_constant_transports_empty_integer_preimages_and_even_cycles(self):
        first = Polynomial(((1, 10**50, 0),))
        second = Polynomial(((1, 0, 10**50),))
        edges = [Observation(0, 1, first, 1, 1), Observation(0, 1, second, 1, 1)]
        result = recover([(1, 10**18)] * 2, edges)
        self.assertEqual(result.values, (1, 1))
        self.assertEqual(result.walks, ())
        self.assertLess(result.evaluations, 300)
        self.assertEqual(
            recover([(1, 4)] * 2, [Observation(0, 1, Polynomial(((1, 2, 0),)), 2, 2)]).status,
            "infeasible",
        )
        addition = Polynomial(((1, 1, 0), (1, 0, 1)))
        ambiguous = [Observation(0, 1, addition, 4, 4)]
        self.assertEqual(recover([(1, 3)] * 2, ambiguous).status, "undetermined")
        self.assertEqual(recover([(1, 1), (1, 3)], ambiguous).values, (1, 3))
        self.assertEqual(
            recover([(1, 1), (1, 3)], ambiguous + [Observation(0, 1, addition, 3, 3)]).status,
            "infeasible",
        )
        self.assertEqual(recover([(1, 1)], [Observation(0, 0, Polynomial(()), 0, 0)]).values, (1,))

    def test_strict_spacing_boundary_diagonal_and_saturated_affine_maps(self):
        # At equality with the destination gap, two values remain possible.
        linear = Polynomial(((100, 0, 1),))
        self.assertEqual(
            recover([(1, 1), (1, 2)], [Observation(0, 1, linear, 100, 200)]).status, "undetermined"
        )
        # The diagonal x*x has gap 3 at x=1, exceeding the separate gaps of 1.
        self.assertEqual(
            recover([(1, 3)], [Observation(0, 0, Polynomial(((1, 1, 1),)), 3, 5)]).values, (2,)
        )
        force_two = Observation(0, 1, Polynomial(((1, 1, 0),)), 2, 2)
        for terms in (((1, 10**100, 1),), ((1, 10**100, 0), (1, 0, 1))):
            impossible = Observation(0, 1, Polynomial(terms), 2, 2)
            self.assertEqual(recover([(1, 3)] * 2, [force_two, impossible]).status, "infeasible")

    def test_odd_walk_reaches_a_root_outside_the_odd_cycle(self):
        linear = Polynomial(((1, 1, 0), (100, 0, 1)))
        truth = (5, 7, 11, 13, 17, 19)
        pairs = ((0, 1), (1, 0), (1, 2), (2, 3), (3, 1), (4, 5))
        edges = [
            Observation(u, v, linear, truth[u] + 100 * truth[v] - 1, truth[u] + 100 * truth[v] + 1)
            for u, v in pairs
        ]
        domains = [(1, 100)] * 6
        domains[4] = (17, 17)
        result = recover(domains, edges)
        self.assertEqual(result.values, truth)
        self.assertTrue(any(root == 0 and len(walk) == 5 for root, walk in result.walks))
        # Exercise SCC and parity traversal beyond Python's usual recursion depth.
        count = 2501
        cycle = [Observation(i, (i + 1) % count, linear, 201, 203) for i in range(count)]
        large = recover([(1, 9)] * count, cycle)
        self.assertEqual(large.values, (2,) * count)
        self.assertEqual(len(large.walks[0][1]), count)

    def test_input_validation_and_immutable_terms(self):
        for terms in (((-1, 1, 1),), ((1, True, 1),), ((1, 1),), ((1, 1.0, 1),)):
            with self.assertRaises(ValueError):
                Polynomial(terms)
        terms = [[1, 1, 1], [2, 1, 1], [0, 7, 7]]
        poly = Polynomial(terms)
        terms[0][0] = 99
        self.assertEqual(poly.terms, ((3, 1, 1),))
        for args in ((0, 1, 10), (1, 1, 0), (True, 1, 10), (1, 1, 1.0)):
            with self.assertRaises(ValueError):
                poly.evaluate(*args)
            with self.assertRaises(ValueError):
                poly.increments(*args)
        for domains, edges in (
            ([], []),
            ([(True, 3)], []),
            ([(2, 1)], []),
            ([(1, 2)], [Observation(0, 1, poly, 1, 1)]),
            ([(1, 2)], [Observation(0, 0, poly, -1, 1)]),
            ([(1, 2)], [Observation(False, 0, poly, 1, 1)]),
            ([(1, 2)], [(0, 0, 1, 2)]),
        ):
            with self.assertRaises(ValueError):
                recover(domains, edges)
