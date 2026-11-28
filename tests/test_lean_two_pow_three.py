"""Tests for the generated p = 3 module (solved/lean_two_pow_three.py, Formal/ICG/TwoPowThree.lean)."""

import random
import unittest
from fractions import Fraction as F
from functools import lru_cache
from itertools import product

from scripts.check_catalogue import ROOT
from solved import lean_icg as li
from solved import lean_two_pow_three as g

P = 3


def f(al, be):
    """f(al, be) = 2 F_3(-al/2, -be/2) = (p-1)|be - al| + |(p-1) al + be|."""
    return (P - 1) * abs(be - al) + abs((P - 1) * al + be)


@lru_cache(maxsize=None)
def exact(n, s, t):
    """Exact value of the chain of length n below the state (s, t), in units of f."""
    if n == 0:
        return 2 * f(s, t)
    return max(f(s - z, t - w) + exact(n - 1, (s + z) / 2, (t + w) / 2) for z, w in g.BITS)


def q3(n, s, t):
    """The value function of TwoPowThree.lean, from the generator's pieces."""
    pt = (s, t)
    if n == 0:
        return max(g.ev(q, pt) for q in g.P0)
    if n == 1:
        return max(g.ev(q, pt) for q in g.P1)
    if n == 2:
        return max(g.ev(q, pt) for q in g.P2)
    rho = F(-1, 2) ** n
    return F(10, 3) * n + F(46, 9) + max(g.ev(g.tp(i, rho), pt) for i in range(4))


def emax(p, a):
    return F(2**a * (3 * a + 4) + 2 * (-1) ** a, 3) * p - F(2**a * (12 * a + 10) + 8 * (-1) ** a, 9)


def rand_point(rng, den=512):
    return F(rng.randint(0, den), den), F(rng.randint(0, den), den)


class Generated(unittest.TestCase):
    def test_committed_file_is_current(self):
        path = ROOT / "formal" / "Formal" / "ICG" / "TwoPowThree.lean"
        self.assertEqual(path.read_text(), g.render())

    def test_certificates_verify(self):
        """Every cell tree is re-checked at the vertices of its cells (render asserts it)."""
        self.assertGreater(g.certificate_summary(), 0)
        g.render()

    def test_no_untrusted_tactics(self):
        text = g.render()
        for word in ("sorry", "native_decide", "admit"):
            self.assertNotIn(word, text)


class ValueFunction(unittest.TestCase):
    def test_base_equals_two_f(self):
        rng = random.Random(1)
        for _ in range(500):
            s, t = rand_point(rng)
            self.assertEqual(q3(0, s, t), 2 * f(s, t))

    def test_matches_exact_chain(self):
        """Q3 n is the exact value of the chain for n <= 5 (direct recursion over all bits)."""
        rng = random.Random(2)
        for n in range(0, 6):
            for _ in range(150):
                s, t = rand_point(rng, 64)
                self.assertEqual(q3(n, s, t), exact(n, s, t), (n, s, t))

    def test_top_state(self):
        for a in range(2, 40):
            self.assertEqual(2 ** (a - 1) * q3(a, F(1), F(0)), emax(P, a), a)
            self.assertLessEqual(q3(a, F(0), F(0)), q3(a, F(1), F(0)))
        self.assertEqual(q3(3, F(0), F(0)), q3(3, F(1), F(0)))  # n = 24: 2^3 can be left out

    def test_closed_form_against_definition(self):
        """max_S E(ICG(2^a * 3, S)) = Emax(3, a), exhaustively over divisor sets (a <= 6)."""
        for a in range(2, 7):
            cells = 2 * (a + 1) - 1
            best = max(li.model_energy(a, 1, P, m) for m in product([False, True], repeat=cells))
            self.assertEqual(best, emax(P, a), a)


class MaximisersAtThree(unittest.TestCase):
    """At p = 3 the maximisers follow the p >= 5 rule for a <= 6, except n = 24 (not claimed in Lean)."""

    def test_rule_at_three(self):
        from tests.test_lean_icg import TwoPowAllExponents

        for a in range(2, 7):
            cells = 2 * (a + 1) - 1
            masks = list(product([False, True], repeat=cells))
            sets = [frozenset((k // 2, k % 2) for k, bit in enumerate(m) if bit) for m in masks]
            values = [li.model_energy(a, 1, P, m) for m in masks]
            winners = {cs for cs, v in zip(sets, values) if v == emax(P, a)}
            ruled = {cs for cs in sets if TwoPowAllExponents.local_rule(a, cs)}
            if a == 3:
                self.assertEqual(len(winners), 6)
                self.assertTrue(ruled < winners)
            else:
                self.assertEqual(winners, ruled, a)


class LemmaStatements(unittest.TestCase):
    """Each generated inequality, evaluated directly at random points (independent of the cells)."""

    def setUp(self):
        self.rng = random.Random(3)
        self.points = [rand_point(self.rng) for _ in range(400)] + [
            (F(i, 8), F(j, 8)) for i in range(9) for j in range(9)
        ]

    def test_upper_lemmas(self):
        for fam, (nxt, _, rhs, _, _, _, _) in g.UP.items():
            for z, w in g.BITS:
                for i, piece in enumerate(nxt):
                    for s, t in self.points:
                        lhs = f(s - z, t - w) + g.ev(g.compose(piece, z, w), (s, t))
                        self.assertLessEqual(lhs, max(g.ev(q, (s, t)) for q in rhs), (fam, z, w, i))

    def test_cover_lemmas(self):
        for (z, w), d in g.COVER.items():
            for i, js in d.items():
                for s, t in self.points:
                    vals = []
                    for j in js:
                        lo, hi = [
                            F(10, 3)
                            + g.ev(g.tp(j, F(-1, 2) * r), (s, t))
                            - f(s - z, t - w)
                            - g.ev(g.compose(g.tp(i, r), z, w), (s, t))
                            for r in (g.LO, g.HI)
                        ]
                        vals.append(min(lo, hi))
                    self.assertGreaterEqual(max(vals), 0, (z, w, i, s, t))

    def test_attainment_lemmas(self):
        for table, cur, nxt in (
            (g.ATT01, g.P1, g.P0),
            (g.ATT12, g.P2, g.P1),
            (g.ATT23, g.W3, g.P2),
        ):
            for j, ((z, w), i) in table.items():
                for s, t in self.points:
                    rhs = f(s - z, t - w) + g.ev(g.compose(nxt[i], z, w), (s, t))
                    self.assertLessEqual(g.ev(cur[j], (s, t)), rhs, (j, z, w, i))


if __name__ == "__main__":
    unittest.main()
