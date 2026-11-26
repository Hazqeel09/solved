import itertools
import unittest
from fractions import Fraction

from solved.chains import catalogue, chains, level
from solved.cycles import Edge, solve


def independent(op, x, y, cap):
    value = {
        "+": lambda: x + y,
        "-": lambda: x - y,
        "*": lambda: x * y,
        "/": lambda: Fraction(x, y),
    }[op]()
    if int(value) != value or not 1 <= value <= cap:
        raise ArithmeticError
    return int(value)


def check_assignment(edges, assignment, cap):
    def path(v, steps):
        for op, k, rev in steps:
            v = independent(op, k, v, cap) if rev else independent(op, v, k, cap)
        return v

    try:
        return all(
            independent(
                e.op,
                path(assignment[e.left], e.left_path),
                path(assignment[e.right], e.right_path),
                cap,
            )
            == e.target
            for e in edges
        )
    except ArithmeticError:
        return False


class CycleTests(unittest.TestCase):
    def test_exhaustive_against_fraction_oracle(self):
        cap = 5
        roots = set(range(1, cap + 1))
        paths = [
            (),
            *(((op, 2, rev),) for op in "+-*/" for rev in (False, True)),
            (("/", 2, True), ("/", 2, True)),
        ]
        for ops in itertools.product("+-*/", repeat=2):
            for j, path in enumerate(paths):
                for t, u in itertools.product(roots, repeat=2):
                    edges = (
                        Edge(0, 1, ops[0], t, path),
                        Edge(1, 0, ops[1], u, (), paths[-j - 1]),
                    )
                    oracle = {
                        x
                        for x in itertools.product(roots, repeat=2)
                        if check_assignment(edges, x, cap)
                    }
                    result = solve(edges, {2}, cap, root_domain=roots)
                    self.assertEqual(set(result.assignments), oracle)
                    self.assertEqual(
                        solve(tuple(reversed(edges)), {2}, cap, root_domain=roots),
                        result,
                    )
                    if result.constrained_by_cycle:
                        self.assertEqual(solve(edges, {2}, cap), result)
                        self.assertLessEqual(len(oracle), 2)

    def test_two_roots_and_tree_transport(self):
        edges = (Edge(7, 31, "+", 5), Edge(31, 7, "*", 6), Edge(31, 22, "-", 1))
        self.assertEqual(solve(edges, (), 10).assignments, ((2, 2, 3), (3, 1, 2)))
        self.assertEqual(solve(edges, (), 10, root_domain={2}).assignments, ((2, 2, 3),))
        self.assertEqual(solve(edges + (Edge(22, 22, "+", 4),), (), 10).assignments, ((2, 2, 3),))

    def test_balance_and_exceptions(self):
        edges = (Edge(0, 1, "+", 9),) * 2
        self.assertFalse(solve(edges, (), 9).enumerated)
        self.assertEqual(len(solve(edges, (), 9, root_domain=set(range(1, 10))).assignments), 8)
        self.assertTrue(solve(edges, (), 9, root_domain=set()).enumerated)
        self.assertEqual(
            solve((Edge(0, 0, "/", 1),), (), 8, root_domain={2, 3}).assignments,
            ((2,), (3,)),
        )
        for bad, cs, cap in [
            ((), (), 5),
            ((Edge(0, 1, "+", 4), Edge(3, 3, "+", 2)), (), 5),
            ((Edge(0, 0, "%", 1),), (), 4),
            ((Edge(True, 0, "*", 1),), (), 4),
            ((Edge(0, 0, "+", 1, (("+", 2, False),)),), (), 5),
            ((Edge(0, 1, "+", 0),), (), 1),
        ]:
            with self.assertRaises(ValueError):
                solve(bad, cs, cap)
        with self.assertRaises(ValueError):
            solve(edges, (), 9, root_domain={True})
        double_inverse = (("/", 2, True), ("/", 2, True))
        self.assertEqual(solve((Edge(0, 0, "+", 6, double_inverse),), {2}, 8).assignments, ())

    def test_large_and_nonsquare(self):
        n = 999_999_937
        self.assertEqual(solve((Edge(0, 0, "*", n * n),), (), 10**18).assignments, ((n,),))
        self.assertFalse(solve((Edge(0, 0, "*", n * n - 1),), (), 10**18).assignments)


class ChainTests(unittest.TestCase):
    def test_boundaries(self):
        self.assertEqual(level(1), 0)
        for k in range(7):
            threshold = 2 ** (2**k)
            self.assertEqual(level(threshold - 1), k)
            self.assertEqual(level(threshold), k + 1)
        for bad in (0, -1, False, 2.0):
            with self.assertRaises(ValueError):
                level(bad)
        with self.assertRaises(ValueError):
            list(chains(3, -1))
        self.assertEqual(catalogue(1)[2], [1, 0, 0])

    def test_compare_unpruned_sequence_search(self):
        # Enumerate by depth using all earlier ordered pairs, with no defect pruning.
        for bound in (2, 7, 17, 32):
            layers = {(1,)}
            expected = set()
            for length in range(level(bound) + 3):
                for row in layers:
                    if length - level(row[-1]) <= 2:
                        expected.add(row)
                layers = {
                    row + (v,)
                    for row in layers
                    for a in row
                    for b in row
                    for v in (a + b, a * b)
                    if row[-1] < v <= bound
                }
            found = list(chains(bound))
            self.assertEqual(len(found), len(expected))
            self.assertEqual({r.values for _, r in found}, expected)
            for defect, r in found:
                self.assertEqual(defect, len(r.recipes) - level(r.values[-1]))
                for j, (op, a, b) in enumerate(r.recipes, 1):
                    self.assertLessEqual(max(a, b), j - 1)
                    self.assertEqual(independent(op, r.values[a], r.values[b], bound), r.values[j])


if __name__ == "__main__":
    unittest.main()
