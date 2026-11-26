import unittest
from itertools import product

from checks.verify_control_cutoffs import controls, verify
from solved.control_basis import admissible_bases, control_cutoff, minimal_basis
from solved.control_profiles import endpoint
from solved.square_controls import Description, expand

PARALLEL = Description(
    (("+", 0, 0), ("squares", 1, None), ("squares", 1, None), ("*", 2, 3)), (1, 1)
)
FERMAT = Description(
    (
        ("+", 0, 0),
        ("+", 1, 0),
        ("squares", 1, None),
        ("+", 3, 0),
        ("squares", 1, None),
        ("+", 5, 0),
        ("*", 4, 6),
        ("*", 2, 7),
    ),
    (1, 1),
)


def exact_member(base, point, excess):
    description = Description(base.control, point)
    # Deliberately use expanded instruction replay and a directly constructed
    # target, not the profile evaluator or bit-length comparison under test.
    return expand(description).values[-1] <= 2 ** (2 ** (description.length - excess)) - 1


class ControlBasisTests(unittest.TestCase):
    def test_complete_three_block_control_census(self):
        certificate = verify()
        self.assertEqual(certificate["controls_by_blocks"], {"0": 1, "1": 3, "2": 24, "3": 360})
        self.assertEqual(certificate["completed_control_excess_families"], 1552)
        self.assertGreater(certificate["finite_replay_points"], 3000)
        with self.assertRaises(ValueError):
            tuple(controls(True))

    def test_two_incomparable_minima_and_exact_fermat_solutions(self):
        for base, excess, expected, cutoff in (
            (PARALLEL, 3, ((2, 3), (3, 2)), 5),
            (FERMAT, 6, ((1, 2), (2, 1)), 4),
        ):
            result = minimal_basis(base, excess)
            self.assertEqual(result.status, "complete")
            self.assertEqual(result.minimals, expected)
            self.assertEqual(result.cutoff, cutoff)
            self.assertEqual(result.unresolved, ())
            for point in product(range(1, 6), repeat=2):
                represented = any(all(a <= b for a, b in zip(p, point)) for p in result.minimals)
                self.assertEqual(represented, exact_member(base, point, excess))
        for point in ((1, 2), (2, 1)):
            self.assertEqual(endpoint(Description(FERMAT.control, point)), 255)

    def test_every_finite_box_has_the_independently_enumerated_basis(self):
        for base, excess in ((PARALLEL, 3), (FERMAT, 6)):
            for upper in product(range(1, 5), repeat=2):
                members = [
                    point
                    for point in product(*(range(1, u + 1) for u in upper))
                    if exact_member(base, point, excess)
                ]
                expected = tuple(
                    p
                    for p in members
                    if not any(q != p and all(a <= b for a, b in zip(q, p)) for q in members)
                )
                result = minimal_basis(base, excess, upper)
                self.assertEqual(result.status, "complete")
                self.assertEqual(result.minimals, expected)

    def test_admissible_lower_corners_cover_exactly_the_domain(self):
        many = (("squares", 0, None),) * 1200
        count, corners = admissible_bases(many, 1201)
        self.assertEqual(count, 1200)
        first = next(corners)
        self.assertEqual(first.runs, (1,) * 1199 + (2,))
        self.assertEqual(next(corners).runs, (1,) * 1198 + (2, 1))
        large = Description(PARALLEL.control, (1, 1))
        count, corners = admissible_bases(large.control, 10**100)
        self.assertEqual(count, 10**100 - 3)
        self.assertEqual(next(corners).runs, (1, 10**100 - 3))
        for excess in range(8):
            count, iterator = admissible_bases(PARALLEL.control, excess)
            bases = tuple(iterator)
            self.assertEqual(count, len(bases))
            for point in product(range(1, 7), repeat=2):
                covered = any(all(a <= b for a, b in zip(base.runs, point)) for base in bases)
                self.assertEqual(covered, 2 + sum(point) >= excess)
        self.assertEqual(admissible_bases((), 1)[0], 0)
        self.assertEqual(control_cutoff((), 1).cutoff, 0)
        self.assertEqual(control_cutoff((), 0).cutoff, 1)
        # A one-shot control iterator must not disappear from the returned record.
        result = control_cutoff(iter(FERMAT.control), 6)
        self.assertEqual(result.control, FERMAT.control)
        self.assertEqual(result.cutoff, 4)

    def test_resource_stops_never_supply_cutoffs(self):
        for kwargs in (
            {"max_queries": 0},
            {"max_queries": 1},
            {"max_bits": 1},
            {"max_regions": 0},
            {"max_regions": 1},
        ):
            result = minimal_basis(PARALLEL, 3, **kwargs)
            self.assertEqual(result.status, "resource_limit", kwargs)
            self.assertIsNone(result.cutoff)
            self.assertTrue(result.unresolved)
            for point in product(range(1, 5), repeat=2):
                excluded = any(all(a <= b for a, b in zip(p, point)) for p in result.minimals)
                if not excluded and exact_member(PARALLEL, point, 3):
                    self.assertTrue(
                        any(
                            all(u is None or g <= u for u, g in zip(box, point))
                            for box in result.unresolved
                        )
                    )
        for kwargs in ({"max_bases": 0}, {"max_queries": 1}, {"max_bases": 1}):
            result = control_cutoff(PARALLEL.control, 6, **kwargs)
            self.assertEqual(result.status, "resource_limit")
            self.assertIsNone(result.cutoff)

    def test_zero_dimensional_domains_and_invalid_options(self):
        self.assertEqual(minimal_basis(Description((), ()), 0).minimals, ((),))
        self.assertEqual(minimal_basis(Description((("+", 0, 0),), ()), 1).minimals, ())
        for kwargs in ({"max_bits": 0}, {"max_queries": True}, {"max_regions": -1}):
            with self.assertRaises(ValueError):
                minimal_basis(PARALLEL, 3, **kwargs)
            with self.assertRaises(ValueError):
                control_cutoff((), 1, **kwargs)
        for upper in ((0, 1), (None,), (True, None)):
            with self.assertRaises(ValueError):
                minimal_basis(PARALLEL, 3, upper)
        self.assertEqual(minimal_basis(PARALLEL, 3, max_bits=None).minimals, ((2, 3), (3, 2)))
