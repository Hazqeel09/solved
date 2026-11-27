import random
import unittest
from itertools import combinations

import sympy

from solved import icg_energy as ie
from solved.icg_families import (
    Order,
    certify,
    certify_maximum_of,
    certify_reference,
    maximisers,
    maximisers_reference,
    p_below_q,
    parity_set,
    q_below_p,
    rectangle,
)

P, Q = sympy.symbols("p q")


def as_sympy(poly):
    return sum(c * P**i * Q**j for (i, j), c in poly.items())


def d(k, x):
    """Jiang-Yang (1.2): d_k(x) = (2k+1) x^k + 4 sum_{j<k} (-1)^(k-j) (j+1) x^j."""
    return (2 * k + 1) * x**k + 4 * sum((-1) ** (k - j) * (j + 1) * x**j for j in range(k))


def g(k, x):
    """Jiang-Yang, same-parity paper: g_k(x) = (x^k (x-1) + 2(-1)^k)/(x+1)."""
    return sympy.cancel((x**k * (x - 1) + 2 * (-1) ** k) / (x + 1))


class EngineTests(unittest.TestCase):
    def test_energy_matches_definition_on_many_orders(self):
        orders = [
            (((2, 1), ("p", 2)), {"p": 5}),
            (((3, 1), ("p", 2)), {"p": 7}),
            (((2, 2), ("p", 1), ("q", 1)), {"p": 3, "q": 5}),
            (((3, 1), ("p", 1), ("q", 1)), {"p": 5, "q": 7}),
            ((("p", 1), ("q", 2)), {"p": 7, "q": 3}),
        ]
        for factors, values in orders:
            order = Order(factors)
            n = 1
            for prime, a in factors:
                n *= (values[prime] if isinstance(prime, str) else prime) ** a
            for r in range(1, len(order.cells) + 1):
                for cells in combinations(order.cells, r):
                    self.assertEqual(
                        order.energy(cells, values),
                        ie.direct_energy(n, order.divisors(cells, values)),
                    )

    def test_fast_and_reference_agree(self):
        cases = [
            ((("p", 2), ("q", 3)), 3),
            (((3, 1), ("p", 2)), 5),
            (((2, 1), ("p", 2)), 3),
            (((2, 3), ("p", 1)), 5),
            (((3, 1), ("p", 1), ("q", 1)), 5),
            (((2, 2), ("p", 2)), 3),
        ]
        for factors, p0 in cases:
            order = Order(factors)
            values = {"p": 7, "q": 11}
            e1, m1 = maximisers(order, values)
            e2, m2 = maximisers_reference(order, values)
            self.assertEqual((e1, sorted(map(sorted, m1))), (e2, sorted(map(sorted, m2))))
            c1 = certify(order, m1, p0, p0)
            c2 = certify_reference(order, m1, p0, p0)
            self.assertEqual(
                (c1.competitors, c1.inequalities, c1.energy),
                (c2.competitors, c2.inequalities, c2.energy),
            )
            wrong = [m1[0] - {sorted(m1[0])[0]}] if len(m1[0]) > 1 else [frozenset(order.cells)]
            with self.assertRaises(ArithmeticError):
                certify(order, wrong, p0, p0)

    def test_region_substitution(self):
        rng = random.Random(7)
        for _ in range(100):
            poly = {(rng.randint(0, 4), rng.randint(0, 4)): rng.randint(-9, 9) for _ in range(5)}
            poly = {k: v for k, v in poly.items() if v}
            p0, q0 = rng.randint(0, 7), rng.randint(0, 7)
            self.assertEqual(rectangle(p0, q0).substitute(poly), ie.shifted(poly, p0, q0))
        x, y = sympy.symbols("x y")
        for region, (sp, sq) in (
            (p_below_q(5), (5 + x, 7 + x + y)),
            (q_below_p(5), (7 + x + y, 5 + y)),
        ):
            poly = {(2, 1): 3, (0, 3): -2, (1, 0): 5}
            expected = sympy.Poly(sympy.expand(3 * sp**2 * sq - 2 * sq**3 + 5 * sp), x, y)
            got = sum(c * x**i * y**j for (i, j), c in region.substitute(poly).items())
            self.assertEqual(sympy.expand(got - expected.as_expr()), 0)


class LiteratureTests(unittest.TestCase):
    def test_sander_sander_squarefree_example(self):
        """E_max(3*5*7) = 520 with unique maximiser {1, 15, 21, 35} (Sander-Sander)."""
        order = Order(((3, 1), (5, 1), (7, 1)))
        best, sets = maximisers(order, {})
        self.assertEqual(best, 520)
        self.assertEqual(
            [sorted(order.divisors(s, {})) for s in sets],
            [[1, 15, 21, 35]],
        )

    def test_jiang_yang_odd_total_exponent(self):
        """arXiv:2608.29523 Thm A: checkerboard maximiser, E = (n + d_a(p) d_b(q))/2."""
        for a, b in ((2, 1), (2, 3), (1, 2), (4, 1)):
            order = Order((("p", a), ("q", b)))
            cert = certify(order, [parity_set(order, 0)], 5, 5)
            expected = (P**a * Q**b + d(a, P) * d(b, Q)) / 2
            self.assertEqual(sympy.expand(as_sympy(cert.energy) - expected), 0)

    def test_jiang_yang_same_parity(self):
        """arXiv:2610.36883 Thm A: exactly D_odd and D_even minus n, E = (n + d d - 2 g g)/2."""
        for a, b in ((1, 1), (2, 2), (1, 3)):
            order = Order((("p", a), ("q", b)))
            cert = certify(order, [parity_set(order, 0), parity_set(order, 1)], 5, 5)
            expected = (P**a * Q**b + d(a, P) * d(b, Q) - 2 * g(a, P) * g(b, Q)) / 2
            self.assertEqual(sympy.expand(as_sympy(cert.energy) - expected), 0)


if __name__ == "__main__":
    unittest.main()


def sander_sander_two_power(s):
    """Maximal-energy exponent sets of ICG(2^s) (Sander-Sander, arXiv:1109.3616, Thm 1.1)."""
    if s == 1:
        return [{0}]
    if s % 2:
        a = set(range(0, s, 2))
        b = {0, *range(1, s - 1, 2), s - 1}
    else:
        a = {*range(0, s - 1, 2), s - 1}
        b = {0, *range(1, s - 2, 2), s - 1}
    return [a] if a == b else [a, b]


def row_parity_set(a, b, rows_odd):
    return frozenset(
        (i, j)
        for i in range(a + 1)
        for j in range(b + 1)
        if (i, j) != (a, b) and j % 2 == (1 if i in rows_odd else 0)
    )


class ClassificationTests(unittest.TestCase):
    def test_parity_law_at_the_prime_three(self):
        for a, b in ((1, 1), (1, 2), (3, 1), (2, 2), (1, 4), (3, 2)):
            order = Order(((3, a), ("p", b)))
            expected = [parity_set(order, 0)] + ([parity_set(order, 1)] if (a + b) % 2 == 0 else [])
            cert = certify(order, expected, region=rectangle(5, 0))
            self.assertGreater(cert.competitors, 0)

    def test_two_adic_correspondence(self):
        for a in range(2, 6):
            for b in (1, 2, 3):
                if (a + 1) * (b + 1) - 1 > 14:
                    continue
                expected = []
                for s in sander_sander_two_power(a):
                    t = s - {0}
                    if b % 2 == 0:
                        t = (t - {a - 1}) | {a}
                    expected.append(row_parity_set(a, b, t))
                order = Order(((2, a), ("p", b)))
                p0 = 5 if (a, b) == (3, 1) else 3
                certify(order, expected, region=rectangle(p0, 0))

    def test_phase_transition_for_2_p2_q(self):
        order = Order(((2, 1), ("p", 2), ("q", 1)))
        a_set = [(0, 0, 0), (0, 0, 1), (0, 2, 0), (0, 2, 1), (1, 0, 0), (1, 1, 1), (1, 2, 0)]
        b_set = [(0, 0, 0), (0, 1, 0), (0, 2, 1), (1, 0, 1), (1, 1, 0), (1, 2, 0)]
        certify(order, [b_set], region=p_below_q(3))
        certify_maximum_of(order, [a_set, b_set], q_below_p(3))
        for p, q in ((11, 7), (103, 101), (127, 109), (131, 107), (151, 127)):
            diff = order.energy(a_set, {"p": p, "q": q}) - order.energy(b_set, {"p": p, "q": q})
            self.assertEqual(diff, 2 * (5 * p * p - 6 * p * q + 9 * q - 8))
        self.assertGreater(
            order.energy(b_set, {"p": 103, "q": 101}), order.energy(a_set, {"p": 103, "q": 101})
        )
        self.assertGreater(
            order.energy(a_set, {"p": 131, "q": 107}), order.energy(b_set, {"p": 131, "q": 107})
        )
        # no ties: (6p - 9) | (5p^2 - 8) forces 2p - 3 | 13, impossible for odd primes p
        for p in sympy.primerange(3, 10**4):
            self.assertNotEqual((5 * p * p - 8) % (6 * p - 9), 0)
