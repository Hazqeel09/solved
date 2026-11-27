import random
import unittest
from fractions import Fraction
from itertools import combinations
from math import comb

import sympy

from solved import intpoly as ip
from solved import matroid_lattice as ml
from solved.matroid_polynomials import polynomials, report


def gaussian_binomial(n, k, q):
    if not 0 <= k <= n:
        return 0
    num = den = 1
    for i in range(k):
        num *= q ** (n - i) - 1
        den *= q ** (i + 1) - 1
    return num // den


def eulerian(n):
    """A_n(x) with A_0 = 1: descents of permutations of n letters."""
    if n == 0:
        return (1,)
    row = [1]
    for m in range(2, n + 1):
        new = [0] * m
        for k in range(m):
            if k < len(row):
                new[k] += (k + 1) * row[k]
            if 0 < k <= len(row):
                new[k] += (m - k) * row[k - 1]
        row = new
    return tuple(row)


def bell(n):
    row = [1]
    for _ in range(n):
        new = [row[-1]]
        for x in row:
            new.append(new[-1] + x)
        row = new
    return row[0]


def sympy_real_roots(p):
    x = sympy.Symbol("x")
    return len(sympy.Poly(list(reversed(p)), x).real_roots())


class IntegerPolynomialTests(unittest.TestCase):
    def test_root_counts_match_sympy_on_constructed_polynomials(self):
        rng = random.Random(20261127)
        for _ in range(250):
            p = ip.ONE
            for _ in range(rng.randint(1, 5)):
                a = rng.randint(-6, 6)
                p = ip.mul(p, (a, 1))  # real root -a
            for _ in range(rng.randint(0, 2)):
                b, c = rng.randint(-5, 5), rng.randint(1, 6)
                p = ip.mul(p, (b * b + c, 2 * b, 1))  # (t+b)^2 + c, no real root
            if rng.random() < 0.3:
                p = ip.mul(p, p)
            self.assertEqual(ip.real_root_count(p), sympy_real_roots(p))
            self.assertEqual(ip.is_real_rooted(p), sympy_real_roots(p) == ip.degree(p))

    def test_interval_counts_and_edge_cases(self):
        p = ip.mul(ip.mul((1, 1), (2, 1)), (0, 1))  # roots 0, -1, -2
        self.assertEqual(ip.real_root_count(p, None, 0), 3)
        self.assertEqual(ip.real_root_count(p, None, -1), 2)
        self.assertEqual(ip.real_root_count(p, -1, 0), 1)
        self.assertTrue(ip.has_only_nonpositive_real_roots(p))
        self.assertFalse(ip.has_only_nonpositive_real_roots((-1, 1)))
        self.assertTrue(ip.is_real_rooted((5,)))
        with self.assertRaises(ValueError):
            ip.is_real_rooted(())
        self.assertFalse(ip.is_real_rooted((1, 0, 1)))
        self.assertTrue(ip.is_real_rooted((1, 2, 1)))

    def test_coefficient_sequences(self):
        self.assertTrue(ip.is_log_concave((1, 3, 3, 1)))
        self.assertFalse(ip.is_log_concave((1, 0, 1)))
        self.assertFalse(ip.is_log_concave((1, 1, 2)))
        self.assertTrue(ip.is_unimodal((1, 2, 2, 1)))
        self.assertFalse(ip.is_unimodal((2, 1, 2)))
        self.assertEqual(ip.gamma_vector((1, 3, 3, 1), 3), (1,))
        self.assertEqual(ip.gamma_vector((4, 15, 20, 15, 4), 4), (4, -1, -2))
        with self.assertRaises(ValueError):
            ip.gamma_vector((1, 2), 2)

    def test_interlacing(self):
        f = ip.mul(ip.mul((1, 1), (3, 1)), (5, 1))
        g = ip.mul((2, 1), (4, 1))
        self.assertTrue(ip.interlaces(f, g))
        self.assertFalse(ip.interlaces(f, ip.mul((2, 1), (2, 1))))
        self.assertFalse(ip.interlaces(f, ip.mul((6, 1), (7, 1))))
        self.assertTrue(ip.interlaces(f, f))


class LatticeConstructionTests(unittest.TestCase):
    def test_flat_counts(self):
        for k in range(0, 6):
            for n in range(k, 8):
                lattice = ml.uniform(k, n)
                expected = sum(comb(n, i) for i in range(k)) + 1
                self.assertEqual(len(lattice), expected)
        for n in range(1, 7):
            self.assertEqual(len(ml.complete_graph(n)), bell(n))
        for r, p in ((3, 2), (4, 2), (3, 3), (5, 2)):
            lattice, points = ml.projective_deletion(r, p)
            self.assertEqual(len(points), gaussian_binomial(r, 1, p))
            self.assertEqual(len(lattice), sum(gaussian_binomial(r, k, p) for k in range(r + 1)))

    def test_projective_flats_agree_with_rank_function_construction(self):
        for r, p, deleted in (
            (3, 2, [(1, 1, 1)]),
            (4, 2, [(1, 0, 0, 0), (0, 1, 1, 0)]),
            (3, 3, []),
        ):
            lattice, points = ml.projective_deletion(r, p, deleted)
            self.assertEqual(lattice, ml.linear(points, p))

    def test_invalid_inputs(self):
        with self.assertRaises(ValueError):
            ml.uniform(3, 2)
        with self.assertRaises(ValueError):
            ml.paving(5, 3, [(0, 1, 2), (0, 1, 3)])
        with self.assertRaises(ValueError):
            ml.projective_deletion(3, 4)
        with self.assertRaises(ValueError):
            ml.projective_deletion(2, 2, [(1, 0), (0, 1)])
        bogus = {0b011: 0b011, 0b101: 0b111}
        with self.assertRaises(ValueError):  # covers of {0} overlap at element 1
            ml.from_closure(3, lambda m: bogus.get(m, m if m.bit_count() <= 1 else 0b111))
        with self.assertRaises(ValueError):  # not closed under intersection
            ml.validate(ml.FlatLattice(3, (0, 0b011, 0b101, 0b111), (0, 1, 1, 2)))

    def test_constructed_lattices_satisfy_flat_axioms(self):
        lattices = [ml.uniform(k, 6) for k in range(7)] + [ml.complete_graph(5)]
        lattices += [
            ml.projective_deletion(4, 2, [(1, 1, 0, 0)])[0],
            ml.paving(7, 3, [(0, 1, 2, 3)]),
        ]
        for lattice in lattices:
            ml.validate(lattice)


class KnownPolynomialTests(unittest.TestCase):
    def test_boolean(self):
        for n in range(0, 6):
            polys = polynomials(ml.boolean(n))
            self.assertEqual(polys.kl, (1,))
            self.assertEqual(polys.inverse_kl, (1,))
            binomial = tuple(comb(n, i) for i in range(n + 1))
            self.assertEqual(polys.z, binomial)
            self.assertEqual(polys.inverse_z, binomial)
            self.assertEqual(polys.chow, eulerian(n) if n else (1,))

    def test_uniform_against_closed_forms(self):
        for d in range(1, 7):
            for m in range(0, 6):
                n = m + d
                polys = polynomials(ml.uniform(d, n))
                # EPW Corollary 2.20: linear coefficient of P.
                if d >= 3:
                    self.assertEqual((polys.kl + (0, 0))[1], comb(n, m + 1) - n)
                # Gao-Xie Theorem 3.3 (m >= 1).
                if m >= 1:
                    q = []
                    for j in range((d - 1) // 2 + 1):
                        c = Fraction(comb(n, d) * m * (d - 2 * j) * comb(d, j), (m + j) * (n - j))
                        self.assertEqual(c.denominator, 1)
                        q.append(int(c))
                    self.assertEqual(polys.inverse_kl, ip.trim(q))
                # Gao-Ruan-Xie Theorem 1.1.
                y = [0] * (d + 1)
                for i in range(d // 2 + 1):
                    y[i] += comb(n, i) * comb(n - i - 1, n - d)
                for i in range((d - 1) // 2 + 1):
                    y[d - i] += comb(n, i) * comb(n - i - 1, n - d)
                self.assertEqual(polys.inverse_z, ip.trim(y))
        # Narayana numbers for U_{d,d+1} (PXY Example 5.3).
        for d in range(1, 8):
            narayana = tuple(comb(d + 1, i + 1) * comb(d + 1, i) // (d + 1) for i in range(d + 1))
            self.assertEqual(polynomials(ml.uniform(d, d + 1)).z, narayana)

    def test_published_examples(self):
        self.assertEqual(polynomials(ml.complete_graph(4)).kl, (1, 1))
        self.assertEqual(polynomials(ml.complete_graph(5)).kl, (1, 5))
        self.assertEqual(polynomials(ml.complete_graph(6)).kl, (1, 16, 15))
        self.assertEqual(polynomials(ml.complete_graph(4)).z, (1, 7, 7, 1))
        self.assertEqual(polynomials(ml.complete_graph(5)).z, (1, 15, 35, 15, 1))
        self.assertEqual(polynomials(ml.uniform(3, 4)).z, (1, 6, 6, 1))
        self.assertEqual(polynomials(ml.uniform(4, 5)).inverse_z, (4, 15, 20, 15, 4))
        self.assertEqual(polynomials(ml.uniform(5, 6)).chow, (1, 51, 161, 51, 1))
        self.assertEqual(polynomials(ml.uniform(2, 3)).chow, (1, 1))

    def test_projective_geometries(self):
        for r, p in ((2, 2), (3, 2), (4, 2), (3, 3), (5, 2)):
            lattice, _ = ml.projective_deletion(r, p)
            polys = polynomials(lattice)
            self.assertEqual(polys.kl, (1,))  # modular lattice (EPW Prop. 2.14)
            self.assertEqual(polys.z, tuple(gaussian_binomial(r, k, p) for k in range(r + 1)))

    def test_direct_sums_are_multiplicative(self):
        pairs = ((ml.uniform(2, 4), ml.uniform(3, 5)), (ml.complete_graph(4), ml.uniform(2, 3)))
        for a, b in pairs:
            pa, pb, ps = polynomials(a), polynomials(b), polynomials(ml.direct_sum(a, b))
            for name in ("kl", "z", "inverse_kl", "inverse_z", "characteristic"):
                self.assertEqual(getattr(ps, name), ip.mul(getattr(pa, name), getattr(pb, name)))


def _relax(size, rank, bases, stressed):
    a = sum(1 << e for e in stressed)
    r = None
    lattice = ml.from_bases(size, bases)
    for f, rk in zip(lattice.flats, lattice.ranks):
        if f == a:
            r = rk
    assert r is not None
    extra = [
        c
        for c in combinations(range(size), rank)
        if (sum(1 << e for e in c) & a).bit_count() >= r + 1
    ]
    return ml.from_bases(size, list(bases) + extra), r


def _paving_bases(size, rank, big):
    masks = [sum(1 << e for e in h) for h in big]
    out = []
    for c in combinations(range(size), rank):
        m = sum(1 << e for e in c)
        if not any(m & h == m for h in masks):
            out.append(c)
    return out


class ValuativityTests(unittest.TestCase):
    """Ferroni-Schroter Thm 3.30: f(Rel(M,A)) + f(U_{k-r,n-h} + U_{r,h}) = f(M) + f(Lambda)."""

    def test_relaxation_identity(self):
        cases = [
            (6, 3, [(0, 1, 2, 3)], (0, 1, 2, 3)),
            (7, 3, [(0, 1, 2), (0, 3, 4), (1, 3, 5)], (0, 1, 2)),
            (8, 4, [(0, 1, 2, 3), (0, 1, 4, 5), (2, 3, 4, 5)], (0, 1, 4, 5)),
            (7, 4, [(0, 1, 2, 3, 4)], (0, 1, 2, 3, 4)),
        ]
        names = ("kl", "z", "inverse_kl", "inverse_z", "chow", "augmented_chow")
        for size, rank, big, stressed in cases:
            bases = _paving_bases(size, rank, big)
            m = polynomials(ml.from_bases(size, bases))
            relaxed_lattice, r = _relax(size, rank, bases, stressed)
            relaxed = polynomials(relaxed_lattice)
            sum_bases = [
                c for c in combinations(range(size), rank) if len(set(c) & set(stressed)) == r
            ]
            lam_bases = [
                c for c in combinations(range(size), rank) if len(set(c) & set(stressed)) >= r
            ]
            direct = polynomials(ml.from_bases(size, sum_bases))
            lam = polynomials(ml.from_bases(size, lam_bases))
            for name in names:
                with self.subTest(case=(size, rank, big), invariant=name):
                    left = ip.add(getattr(relaxed, name), getattr(direct, name))
                    right = ip.add(getattr(m, name), getattr(lam, name))
                    self.assertEqual(left, right)


class SparsePavingTests(unittest.TestCase):
    def test_inverse_z_formula(self):
        """Gao-Ruan-Xie Theorem 1.3 on sparse paving matroids with several circuit-hyperplanes."""
        cases = [
            (6, 3, [(0, 1, 2), (3, 4, 5)]),
            (7, 3, [(0, 1, 2), (0, 3, 4), (0, 5, 6), (1, 3, 5)]),
            (8, 4, [(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 5), (2, 3, 6, 7)]),
            (9, 4, [(0, 1, 2, 3), (4, 5, 6, 7), (0, 1, 4, 8), (2, 5, 6, 8)]),
        ]
        for size, k, circuit_hyperplanes in cases:
            lam = len(circuit_hyperplanes)
            sparse = polynomials(ml.paving(size, k, circuit_hyperplanes))
            unif = polynomials(ml.uniform(k, size))
            correction = [comb(k, i) for i in range(k + 1)]
            if k % 2 == 0:
                catalan = comb(k, k // 2) // (k // 2 + 1)
                correction[k // 2] -= catalan
            expected = ip.sub(unif.inverse_z, ip.scale(ip.trim(correction), lam))
            self.assertEqual(sparse.inverse_z, expected)


class ReportTests(unittest.TestCase):
    def test_small_matroids_satisfy_open_conjectures(self):
        lattices = [ml.uniform(k, n) for n in range(1, 8) for k in range(1, n + 1)]
        lattices += [ml.complete_graph(n) for n in range(2, 7)]
        lattices.append(ml.projective_deletion(4, 2, [(1, 0, 0, 0)])[0])
        for lattice in lattices:
            self.assertEqual(report(polynomials(lattice)).open_conjecture_failures(), [])


if __name__ == "__main__":
    unittest.main()
