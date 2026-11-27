import unittest
from itertools import combinations

import sympy

from solved import icg_energy as ie


def cells_to_divisors(cells, p, q):
    return [p**a * q**b for a, b in cells]


class ModelTests(unittest.TestCase):
    def test_factorized_energy_matches_definition(self):
        """Every one of the 2,047 divisor sets, at prime pairs in both orders."""
        for p, q in ((3, 5), (5, 3), (3, 7), (7, 3), (5, 7), (7, 5), (3, 11), (11, 3)):
            n = p * p * q**3
            for r in range(1, len(ie.CELLS) + 1):
                for cells in combinations(ie.CELLS, r):
                    self.assertEqual(
                        ie.energy(cells, p, q),
                        ie.direct_energy(n, cells_to_divisors(cells, p, q)),
                    )

    def test_star_energy_matches_published_closed_form(self):
        """Roldan, arXiv:2604.09491, Theorem 1.2 (Eq. 7)."""
        p, q = sympy.symbols("p q")
        paper = (
            (5 * p**2 - 8 * p + 4) * (q - 1) * (3 * q**2 - 2 * q + 1)
            + (p - 1) * (2 * p - 1) * (q**3 - 2 * q**2 + 2 * q - 2)
            + (p**2 - 2 * p + 2) * (q - 1) * (q**2 + 1)
            + (p - 1) * q**3
        )
        ours = sum(c * p**i * q**j for (i, j), c in ie.star_energy_polynomial().items())
        self.assertEqual(sympy.expand(ours - paper), 0)

    def test_ramanujan_sums(self):
        for m in range(1, 60):
            for j in range(0, 60):
                direct = sum(
                    sympy.exp(2 * sympy.pi * sympy.I * a * j / m)
                    for a in range(1, m + 1)
                    if sympy.gcd(a, m) == 1
                )
                self.assertEqual(ie.ramanujan(j, m), int(sympy.nsimplify(sympy.N(direct, 30))))

    def test_polynomial_helpers(self):
        poly = ie.padd(ie.pmul(ie.P, ie.P), ie.pscale(ie.Q, -5), ie.pconst(7))  # p^2 - 5q + 7
        self.assertEqual(ie.shifted(poly, 3, 3), {(2, 0): 1, (1, 0): 6, (0, 1): -5, (0, 0): 1})
        self.assertIsNone(ie.certified_sign(poly, 3, 3))
        self.assertEqual(ie.certified_sign(ie.padd(ie.P, ie.pconst(-3)), 3, 3), 1)
        self.assertEqual(ie.certified_sign({}, 3, 3), 0)
        self.assertFalse(ie.certified_positive(ie.padd(ie.P, ie.pconst(-3)), 3, 3))
        self.assertEqual(ie.evaluate(poly, 4, 2), 13)


class ProofTests(unittest.TestCase):
    def test_certificate_on_whole_domain(self):
        cert = ie.prove(3, 3)
        self.assertEqual(cert.divisor_sets, 2046)
        self.assertGreaterEqual(cert.inequalities, cert.divisor_sets)

    def test_brute_force_agrees_for_small_primes(self):
        primes = list(sympy.primerange(3, 60))
        for p in primes:
            for q in primes:
                if p == q:
                    continue
                values = {
                    frozenset(cells): ie.energy(cells, p, q)
                    for r in range(1, len(ie.CELLS) + 1)
                    for cells in combinations(ie.CELLS, r)
                }
                best = max(values.values())
                self.assertEqual([s for s, v in values.items() if v == best], [ie.STAR])

    def test_certificate_detects_a_wrong_maximiser(self):
        """The method is not vacuous: claiming another set as maximiser must fail."""
        original = ie.STAR
        try:
            ie.STAR = frozenset({(0, 0), (2, 0), (1, 1), (0, 2), (2, 2)})
            with self.assertRaises(ArithmeticError):
                ie.prove(3, 3)
        finally:
            ie.STAR = original

    def test_certificate_rejects_domain_including_p_equal_one(self):
        with self.assertRaises(ArithmeticError):
            ie.prove(1, 1)


if __name__ == "__main__":
    unittest.main()
