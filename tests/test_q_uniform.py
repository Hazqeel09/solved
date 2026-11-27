import unittest

from solved import matroid_lattice as ml
from solved import native_lattice as nl
from solved.matroid_polynomials import polynomials
from solved.q_uniform import QUniform, gaussian

NAMES = ("characteristic", "kl", "z", "inverse_kl", "inverse_z", "chow", "augmented_chow")


def assert_same(test, got, expected, **label):
    for name in NAMES:
        with test.subTest(invariant=name, **label):
            test.assertEqual(getattr(got, name), getattr(expected, name))


class FreeExtensionTests(unittest.TestCase):
    def test_free_extension_matches_rank_function(self):
        for base in (ml.uniform(2, 3), ml.uniform(3, 5), ml.complete_graph(4)):
            ext = ml.free_extension(base)
            ml.validate(ext)
            r = base.rank
            flats = base.flats

            def rank(mask, flats=flats, r=r, size=base.size):
                inner = mask & ((1 << size) - 1)
                k = min(rk for f, rk in zip(flats, base.ranks) if f & inner == inner)
                return min(k + (mask >> size & 1), r)

            self.assertEqual(ext, ml.from_rank_function(base.size + 1, rank))
        self.assertEqual(ml.free_extension(ml.uniform(2, 3)), ml.uniform(2, 4))


class QUniformTests(unittest.TestCase):
    def test_q_equal_one_is_uniform(self):
        engine = QUniform(1)
        for n in range(0, 9):
            for k in range(0, n + 1):
                for m in range(0, 3):
                    expected = polynomials(ml.uniform(k, n + m))
                    assert_same(self, engine.polynomials(n, k, m), expected, n=n, k=k, m=m)

    def test_truncated_projective_geometries(self):
        for q, nmax in ((2, 6), (3, 4), (5, 3)):
            engine = QUniform(q)
            for n in range(1, nmax + 1):
                lattice, _ = ml.projective_deletion(n, q)
                for k in range(0, n + 1):
                    truncated = ml.truncation(lattice, k)
                    expected = polynomials(truncated, nl.interval_characteristic(truncated))
                    assert_same(self, engine.polynomials(n, k), expected, q=q, n=n, k=k)

    def test_free_points_on_truncated_geometries(self):
        for q, n, k, mmax in ((2, 4, 4, 4), (2, 5, 3, 3), (3, 3, 3, 4), (3, 4, 4, 2), (5, 3, 2, 3)):
            engine = QUniform(q)
            lattice = ml.truncation(ml.projective_deletion(n, q)[0], k)
            for m in range(0, mmax + 1):
                expected = polynomials(lattice, nl.interval_characteristic(lattice))
                assert_same(self, engine.polynomials(n, k, m), expected, q=q, n=n, k=k, m=m)
                lattice = ml.free_extension(lattice)

    def test_gaussian_and_inputs(self):
        self.assertEqual([gaussian(4, k, 2) for k in range(5)], [1, 15, 35, 15, 1])
        self.assertEqual([gaussian(5, k, 1) for k in range(6)], [1, 5, 10, 10, 5, 1])
        self.assertEqual(gaussian(3, 4, 2), 0)
        with self.assertRaises(ValueError):
            QUniform(0)
        with self.assertRaises(ValueError):
            QUniform(2).kl(2, 3)
        with self.assertRaises(ValueError):
            QUniform(2).kl(3, 2, -1)


if __name__ == "__main__":
    unittest.main()
