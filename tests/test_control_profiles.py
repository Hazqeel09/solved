import random
import unittest
from itertools import product

from solved.chains import chains
from solved.control_profiles import (
    Profile,
    ResourceLimit,
    endpoint,
    ideal_intersection,
    in_upset,
    profile,
)
from solved.square_controls import Description, encode, expand, validate


def random_control(rng, steps):
    control = []
    runs = []
    for i in range(steps):
        op = rng.choice(("+", "*", "squares"))
        a = rng.randrange(i + 1)
        if op == "squares":
            control.append((op, a, None))
            runs.append(rng.randrange(1, 3))
        else:
            control.append((op, a, rng.randrange(i + 1)))
    return Description(tuple(control), tuple(runs))


class ControlProfileTests(unittest.TestCase):
    def test_encoded_increasing_chains_with_every_free_subset(self):
        checked = 0
        for _, chain in chains(64, 1):
            base = encode(chain)
            for mask in product((False, True), repeat=len(base.runs)):
                free = tuple(i for i, selected in enumerate(mask) if selected)
                bound = profile(base, free)
                for t in range(3):
                    shifted = Description(
                        base.control,
                        tuple(g + t if i in free else g for i, g in enumerate(base.runs)),
                    )
                    actual = expand(shifted).values[-1]
                    self.assertLessEqual(bound.leading_lower(2**t), actual)
                    self.assertLessEqual(actual, bound.upper(2**t))
                    checked += 1
        self.assertEqual(checked, 201)

    def test_integer_ratio_witness_when_ceiling_logs_have_no_gap(self):
        base = Description((("+", 0, 0), ("+", 1, 0), ("squares", 2, None), ("+", 3, 3)), (1,))
        decision = ideal_intersection(base, 2)
        self.assertEqual(decision.method, "integer_ratio")
        self.assertEqual(decision.bound.bases, (2, 9))
        self.assertTrue(in_upset(Description(base.control, decision.witness), 2))

    def test_symbolic_bounds_against_exact_program_families(self):
        rng = random.Random(271131)
        for _ in range(1000):
            base = random_control(rng, rng.randrange(1, 7))
            free = tuple(
                rng.sample(range(len(base.runs)), min(3, rng.randrange(len(base.runs) + 1)))
            )
            bound = profile(base, free)
            self.assertEqual(endpoint(base), expand(base).values[-1])
            for t in range(3):
                runs = tuple(g + t if i in free else g for i, g in enumerate(base.runs))
                actual = endpoint(Description(base.control, runs))
                self.assertLessEqual(bound.leading_lower(2**t), actual)
                self.assertLessEqual(actual, bound.upper(2**t))
                if not free:
                    self.assertEqual(bound.bases, (actual,))

    def test_empty_ideal_certificates_against_exhaustive_finite_boxes(self):
        rng = random.Random(271132)
        empty = 0
        witnessed = 0
        for _ in range(500):
            base = random_control(rng, rng.randrange(1, 6))
            excess = rng.randrange(base.length + 1)
            upper = tuple(g + rng.randrange(2) if rng.randrange(2) else None for g in base.runs)
            decision = ideal_intersection(base, excess, upper)
            if decision.empty:
                empty += 1
                for runs in product(
                    *(
                        range(g, (u if u is not None else g + 3) + 1)
                        for g, u in zip(base.runs, upper)
                    )
                ):
                    self.assertFalse(in_upset(Description(base.control, runs), excess))
            else:
                self.assertIsNotNone(decision.witness)
                self.assertTrue(all(u is None or g <= u for g, u in zip(decision.witness, upper)))
                try:
                    self.assertTrue(in_upset(Description(base.control, decision.witness), excess))
                    witnessed += 1
                except ResourceLimit:
                    # The symbolic witness can be far larger than a directly replayable integer.
                    self.assertGreater(decision.shift, 0)
        self.assertGreater(empty, 20)
        self.assertGreater(witnessed, 100)

    def test_unused_runs_huge_counts_and_exact_zero_dimensional_cases(self):
        unused = Description((("squares", 0, None), ("+", 0, 0)), (10**100,))
        bound = profile(unused)
        self.assertEqual(bound.bases, (2,))
        self.assertEqual(bound.leading_lower(10**100), 1)
        decision = ideal_intersection(unused, 0)
        self.assertFalse(decision.empty)
        self.assertEqual(decision.shift, 0)
        self.assertEqual(endpoint(unused), 2)
        unused_large = Description((("+", 0, 0), ("squares", 1, None), ("+", 0, 0)), (10**100,))
        self.assertEqual(endpoint(unused_large, max_bits=2), 2)
        self.assertEqual(profile(unused_large, max_bits=2).bases, (2,))
        self.assertEqual(profile(unused_large).free_count, 1)
        self.assertEqual(unused_large.length, 10**100 + 2)
        self.assertFalse(ideal_intersection(Description((), ()), 0).empty)
        self.assertTrue(ideal_intersection(Description((("+", 0, 0),), ()), 1).empty)
        powers = Description((("+", 0, 0), ("squares", 1, None)), (1,))
        self.assertTrue(ideal_intersection(powers, 1).empty)

    def test_resource_limits_are_explicit_and_do_not_mean_empty(self):
        # Cap internal exponents too, before exponentiation can allocate them.
        distant = Profile((1,) * 2000 + (2,), 2000)
        for evaluate in (distant.upper, distant.leading_lower):
            with self.assertRaises(ResourceLimit):
                evaluate(10**100, max_bits=2)
        large = Description((("+", 0, 0), ("squares", 1, None)), (100,))
        for action in (
            lambda: profile(large, max_bits=1024),
            lambda: endpoint(large, max_bits=1024),
            lambda: ideal_intersection(large, 1, max_bits=1024),
        ):
            with self.assertRaises(ResourceLimit):
                action()
        edge = Description((("+", 0, 0), ("squares", 1, None)), (10,))
        self.assertEqual(endpoint(edge, max_bits=1025).bit_length(), 1025)
        with self.assertRaises(ResourceLimit):
            endpoint(edge, max_bits=1024)

    def test_validation_without_evaluating_arithmetic(self):
        huge = Description((("+", 0, 0), ("squares", 1, None)), (10**100,))
        self.assertEqual(validate(huge), huge)
        for desc in (
            Description((("+", True, 0),), ()),
            Description((("squares", 0, None),), ()),
            Description((), (1,)),
            Description((("bad", 0, 0),), ()),
            Description((("squares", 0, None),), (0,)),
        ):
            with self.assertRaises(ValueError):
                validate(desc)
        for free in ((0, 0), (True,), (-1,), (1,)):
            with self.assertRaises(ValueError):
                profile(huge, free)
        small = Description((("+", 0, 0), ("squares", 1, None)), (1,))
        for excess, upper in ((True, None), (3, None), (0, ()), (0, (0,)), (0, (True,))):
            with self.assertRaises(ValueError):
                ideal_intersection(small, excess, upper)
        with self.assertRaises(ValueError):
            Profile((0,), 0)
        with self.assertRaises(ValueError):
            Profile((1, 2), 0)
        with self.assertRaises(ValueError):
            Profile((1,), 0).coefficient(-1)
