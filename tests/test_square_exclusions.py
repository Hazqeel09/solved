import unittest
from itertools import product
from unittest.mock import patch

from solved.chains import Chain, chains
from solved.square_controls import Description, encode, expand
from solved.square_exclusions import OrthantCertificate, compare_tower_minus_one


class ExclusionTests(unittest.TestCase):
    def test_comparison_matches_materialized_targets(self):
        for n in range(9):
            target = (1 << (1 << n)) - 1
            values = {1, max(1, target - 1), target, target + 1, target * 2}
            values.update(range(1, 200))
            for value in values:
                self.assertEqual(
                    compare_tower_minus_one(value, n), (value > target) - (value < target)
                )
        self.assertEqual(compare_tower_minus_one(65535, 10**100), -1)
        for value, index in ((True, 1), (0, 1), (3, True), (3, -1), (3.0, 1)):
            with self.assertRaises(ValueError):
                compare_tower_minus_one(value, index)

    def test_all_small_controls_and_inflations(self):
        certificates = covered = solutions = 0
        for _, chain in chains(128, 3):
            base = encode(chain)
            for excess in range(1, min(4, base.length + 1)):
                cmp = compare_tower_minus_one(chain.values[-1], base.length - excess)
                if cmp > 0:
                    with self.assertRaises(ValueError):
                        OrthantCertificate(base, excess)
                    continue
                certificate = OrthantCertificate(base, excess)
                certificates += 1
                solutions += certificate.base_is_solution
                self.assertEqual(certificate.excludes(base, excess), cmp < 0)
                for delta in product(range(2), repeat=len(base.runs)):
                    candidate = Description(
                        base.control, tuple(x + y for x, y in zip(base.runs, delta))
                    )
                    if certificate.excludes(candidate, excess):
                        endpoint = expand(candidate).values[-1]
                        self.assertEqual(
                            compare_tower_minus_one(endpoint, candidate.length - excess), -1
                        )
                        covered += 1
        self.assertGreater(certificates, 500)
        self.assertGreater(covered, 1000)
        self.assertGreater(solutions, 0)

    def test_exact_base_and_huge_extension(self):
        # Membership checks remain finite even when the candidate would be enormous.
        chain = Chain((1, 2, 4, 16, 17), (("+", 0, 0), ("*", 1, 1), ("*", 2, 2), ("+", 3, 0)))
        base = encode(chain)
        certificate = OrthantCertificate(base, 1)
        self.assertFalse(certificate.base_is_solution)
        far = Description(base.control, (10**100,))
        with patch("solved.square_exclusions.expand", side_effect=AssertionError("expanded query")):
            self.assertTrue(certificate.excludes(far, 1))
        exact = encode(
            Chain(
                (1, 2, 4, 5, 10, 15),
                (("+", 0, 0), ("*", 1, 1), ("+", 2, 0), ("*", 3, 1), ("+", 4, 3)),
            )
        )
        c = OrthantCertificate(exact, 3)
        self.assertTrue(c.base_is_solution)
        self.assertFalse(c.excludes(exact, 3))
        extension = Description(exact.control, (2,))
        self.assertTrue(c.excludes(extension, 3))
        self.assertEqual(expand(extension).values[-1], 51)

    def test_incomparable_controls_excess_and_mutation(self):
        chain = Chain(
            (1, 2, 4, 16, 256, 272),
            (("+", 0, 0), ("*", 1, 1), ("*", 2, 2), ("*", 3, 3), ("+", 4, 3)),
        )
        base = encode(chain)
        self.assertEqual(base.runs, (2, 1))
        certificate = OrthantCertificate(base, 1)
        self.assertFalse(certificate.excludes(Description(base.control, (1, 3)), 1))
        self.assertFalse(certificate.excludes(base, 2))
        self.assertFalse(certificate.excludes(Description((("+", 0, 0),), ()), 1))
        with self.assertRaises(ValueError):
            certificate.excludes(Description(base.control, (1,)), 1)
        for runs in ((0, 2), (True, 2), (1.0, 2)):
            with self.assertRaises(ValueError):
                certificate.excludes(Description(base.control, runs), 1)
        control = [list(s) for s in base.control]
        runs = list(base.runs)
        copy = OrthantCertificate(Description(control, runs), 1)
        runs[0] = 100
        control[0][0] = "-"
        self.assertEqual(copy.base, base)
        for excess in (-1, True, 1.0, base.length + 1):
            with self.assertRaises(ValueError):
                OrthantCertificate(base, excess)
