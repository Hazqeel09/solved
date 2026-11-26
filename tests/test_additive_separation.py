import unittest

from checks.verify_additive_separation import execute, normalize, signed_mersenne, verify


class AdditiveSeparationTests(unittest.TestCase):
    def test_general_am_normalization_models(self):
        result = verify()
        self.assertGreater(result["normalization"]["programs"], 750)
        for name, count in result["normalization"].items():
            self.assertGreater(count, 100, name)
        self.assertEqual([case["am_minimum"] for case in result["small_examples"]], [2, 4, 6, 8])
        self.assertEqual(result["negative_and_zero_trace"], (1, 0, -1, 1))

    def test_identity_decreasing_writes_and_unused_overshoots(self):
        tape = (("+", 0, 0), ("*", 1, 1), ("+", 0, 0), ("*", 0, 1), ("+", 1, 0))
        self.assertEqual(execute(tape), (1, 2, 4, 2, 2, 3))
        chain = normalize(tape)
        self.assertEqual(chain.values, (1, 2, 3))
        self.assertEqual(len(chain.recipes), 2)
        self.assertEqual(normalize((("+", 0, 0), ("*", 0, 0))).values, (1,))
        self.assertEqual(normalize(()).values, (1,))
        self.assertEqual(normalize(iter(tape)), chain)

    def test_signed_witness_counts_all_squares_and_subtraction(self):
        for n in range(13):
            tape = signed_mersenne(n)
            self.assertEqual(len(tape), n + 2)
            self.assertEqual(sum(op == "*" for op, _, _ in tape), n)
            self.assertEqual(execute(tape, signed=True)[-1], (1 << (1 << n)) - 1)
        # The constructor is an upper bound, not a claimed optimum for n=0 or 1.
        self.assertEqual(execute(signed_mersenne(0), signed=True)[-1], 1)
        self.assertEqual(execute((), signed=True), (1,))

    def test_reject_invalid_models_and_forward_references(self):
        for tape in (
            (("/", 0, 0),),
            (("+", 1, 0),),
            (("+", True, 0),),
            (("+", False, 0),),
            ((["+"], 0, 0),),
            (("*", 0.0, 0),),
            (("+", -1, 0),),
            (("+", 0),),
        ):
            for signed in (False, True):
                with self.assertRaises(ValueError):
                    execute(tape, signed=signed)
        with self.assertRaises(ValueError):
            normalize((("-", 0, 0),))
        with self.assertRaises(ValueError):
            execute((), signed=1)
        for n in (-1, True, 1.0):
            with self.assertRaises(ValueError):
                signed_mersenne(n)
