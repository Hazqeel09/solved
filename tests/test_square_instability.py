import unittest

from checks.verify_square_instability import (
    first_exception,
    power_minima,
    power_witness,
    replay,
    verify,
)


class InstabilityTests(unittest.TestCase):
    def test_counterexample_and_two_exhaustive_lower_bounds(self):
        result = verify()
        self.assertEqual([r["length"] for r in result["cases"]], [8, 8])
        self.assertEqual([r["target"] for r in result["cases"]], [267, 71289])
        self.assertEqual(
            [r["lower_bound_sequence_counts"] for r in result["cases"]],
            [[5, 43, 529, 7046], [6, 103, 2598]],
        )

    def test_witnesses_on_the_infinite_ray(self):
        for k in range(1, 9):
            witness = power_witness(k)
            self.assertEqual(replay(witness), 267 ** (1 << k))
            self.assertEqual(len(witness) - 1, k + 7)
        self.assertEqual([r["minimum_length"] for r in power_minima(2)["powers"]], [8, 9])

    def test_prime_support_alone_does_not_exclude_low_defect(self):
        from solved.chains import level

        witness = (
            1,
            2,
            3,
            9,
            81,
            729,
            531441,
            282429536481,
            79766443076872509863361,
            79766443076872509863442,
        )
        endpoint = replay(witness)
        self.assertEqual(endpoint, 3**48 + 81)
        self.assertEqual(endpoint % 89, 0)
        self.assertEqual(len(witness) - 1 - level(endpoint), 2)

    def test_small_initial_segment_and_input_contracts(self):
        self.assertEqual(first_exception(25)["exceptions"], [])
        for k in (0, -1, True, 1.5):
            with self.assertRaises(ValueError):
                power_witness(k)
        for witness in ((), (True, 2), (1.0, 2), (1, 1), (1, 2, 7), (2, 4), (1, 2, 2.5)):
            with self.assertRaises(ValueError):
                replay(witness)
