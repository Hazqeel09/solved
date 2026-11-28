"""Tests for the 2p^b energy modules (solved/lean_two_pb.py, formal/Formal/ICG/TwoPb/).

The Lean build re-checks every certificate; these tests compare the generator's data with independent
oracles: the exact chain recursion, the Ramanujan-sum energy (solved.icg_energy.direct_energy) and the
eigenvalues of the circulant adjacency matrix itself."""

import cmath
import random
import re
import unittest
from fractions import Fraction as F
from functools import lru_cache
from itertools import combinations
from math import gcd

from sympy import Poly, Rational

from scripts.check_catalogue import ROOT
from solved import lean_two_pb as g
from solved.icg_energy import direct_energy

CORNERS = [(0, 0), (1, 0), (0, 1), (1, 1)]


def closed(p, b):
    eps = [1, -1, -1, 1]
    return 2 * sum(eps[j % 4] * (b + 1 - j) * p ** (b - j) for j in range(b + 1))


def chain_exact(p, n):
    """Exact value V_n(s, t) of the chain with n steps left (x = 1/p), by recursion over corners."""
    x = F(1, p)

    @lru_cache(maxsize=None)
    def V(m, s, t):
        if m == 0:
            return 2 * max(s, t)
        return max(
            2 * (1 - x) * max(abs(c - s), abs(d - t))
            + V(m - 1, x * s + (1 - x) * c, x * t + (1 - x) * d)
            for c, d in CORNERS
        )

    return lambda s, t: V(n, s, t)


@lru_cache(maxsize=None)
def model():
    return g.Model(g.load())


@lru_cache(maxsize=None)
def scaled_pieces(k):
    gens = (g.y, g.tau, g.s, g.t)
    return [Poly(q, *gens) for q in model().Qh[k]]


def rat(v):
    return Rational(v.numerator, v.denominator)


def W(p, n, s, t):
    """W_n(s, t) from the generated pieces: (n Kg + max_i Qh_{n mod 4, i}(y, tau_n, s, t)) / K."""
    m = model()
    y = rat(F(p - 3))
    tau_n = rat(F(1, p) ** (n - m.m[n % 4]))
    K = Poly(m.K, g.y).eval(y)
    Kg = Poly(m.Kg, g.y).eval(y)
    best = max(q.eval((y, tau_n, rat(s), rat(t))) for q in scaled_pieces(n % 4))
    v = (n * Kg + best) / K
    return F(int(v.p), int(v.q))


class ValueFunction(unittest.TestCase):
    def test_upper_bound_and_exactness(self):
        """W_n >= V_n for 1 <= n <= 6, with equality for n = 5, 6, at grid and random points."""
        rng = random.Random(20261128)
        pts = [(F(i, 4), F(j, 4)) for i in range(5) for j in range(5)]
        pts += [(F(rng.randint(0, 999), 999), F(rng.randint(0, 999), 999)) for _ in range(12)]
        for p in (3, 5, 7):
            for n in range(1, 7):  # 4^n paths per point; exactness starts at n = 5
                V = chain_exact(p, n)
                for s, t in pts:
                    w, v = W(p, n, s, t), V(s, t)
                    self.assertGreaterEqual(w, v, (p, n, s, t))
                    if n >= 5:
                        self.assertEqual(w, v, (p, n, s, t))

    def test_start_value_is_closed_form(self):
        for p in (3, 5, 7, 11, 101):
            for b in range(2, 21):
                self.assertEqual(W(p, b, F(1), F(0)) * p**b, closed(p, b), (p, b))
                self.assertLessEqual(W(p, b, F(0), F(0)) * p**b, closed(p, b), (p, b))


class GraphEnergy(unittest.TestCase):
    def test_closed_form_is_the_exhaustive_maximum(self):
        """Exact energies of every divisor set (Ramanujan sums); the Lean maximiser is a maximiser."""
        for p, b in [(3, 1), (3, 2), (3, 3), (3, 4), (5, 1), (5, 2), (5, 3), (7, 2), (11, 1)]:
            n = 2 * p**b
            divs = [d for d in range(1, n) if n % d == 0]
            best = max(
                direct_energy(n, list(S))
                for r in range(1, len(divs) + 1)
                for S in combinations(divs, r)
            )
            self.assertEqual(best, closed(p, b), (p, b))
            self.assertEqual(direct_energy(n, sorted(lean_maximiser(p, b))), closed(p, b), (p, b))

    def test_adjacency_eigenvalues(self):
        """The adjacency matrix of ICG(n, S*) has energy equal to the closed form. Its first row is
        a_k = [k != 0 and gcd(k, n) in S*]; a circulant matrix has eigenvalues sum_k a_k w^(jk),
        w = exp(2 pi i / n), computed here directly (independent of the Ramanujan-sum formula)."""
        for p, b in [(3, 2), (3, 3), (5, 2), (7, 1)]:
            n = 2 * p**b
            S = lean_maximiser(p, b)
            row = [1 if k and gcd(k, n) in S else 0 for k in range(n)]
            eig = [
                sum(a * cmath.exp(2j * cmath.pi * j * k / n) for k, a in enumerate(row))
                for j in range(n)
            ]
            self.assertTrue(all(abs(e.imag) < 1e-9 for e in eig))
            self.assertAlmostEqual(sum(abs(e.real) for e in eig), closed(p, b), places=6)


def lean_maximiser(p, b):
    """setP p b (zOpt b) (wOpt b) of Attain.lean: p^b and the cells of the corner 4-cycle walk."""
    cyc = g.FWD if b % 4 in (0, 3) else g.REV
    S = {p**b}
    for k in range(b):
        z, w = cyc[(b - 1 - k) % 4]
        if z:
            S.add(p**k)
        if w:
            S.add(2 * p**k)
    return S


class Certificates(unittest.TestCase):
    def test_data_shape(self):
        data = g.load()
        self.assertEqual(data["n0"], 1)
        self.assertEqual(len(data["steps"]), sum(len(model().Qh[k]) for k in range(4)) * 8)
        self.assertEqual(len(data["base"]), 16)
        for k in range(4):
            sig = model().sigma[k]
            self.assertTrue(all(sig[sig[i]] == i != sig[i] for i in range(len(sig))))

    def test_attainment_is_periodic(self):
        start, table, base = g.attain_data(model())
        self.assertEqual(len(table), 16)
        self.assertEqual(set(base), {0, 1, 2, 3})

    def test_generated_modules_have_no_untrusted_tactics(self):
        bad = re.compile(
            r"\b(sorry|native_decide|admit|implemented_by|unsafe)\b|debug\.skipKernelTC"
        )
        for path in g.OUT.glob("*.lean"):
            self.assertIsNone(bad.search(path.read_text()), path.name)

    def test_generated_modules_are_registered(self):
        formal = (ROOT / "formal" / "Formal.lean").read_text()
        self.assertIn("import Formal.ICG.TwoPb.Max", formal)
        audit = (ROOT / "formal" / "FormalTests" / "Axioms.lean").read_text()
        self.assertIn("#print axioms Solved.ICG.TwoPb.energy_max_all", audit)


if __name__ == "__main__":
    unittest.main()
