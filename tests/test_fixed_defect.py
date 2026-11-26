import itertools
import unittest
from fractions import Fraction
from math import comb

from solved.chains import Chain, chains, level
from solved.counting import nested_coordinates, nested_witness
from solved.fixed_defect import Description, Segment, decode, encode, radius


def build(ops):
    row = [1]
    rules = []
    for op, a, b in ops:
        row.append(row[a] + row[b] if op == "+" else row[a] * row[b])
        rules.append((op, a, b))
    return Chain(tuple(row), tuple(rules))


class FixedDefectTests(unittest.TestCase):
    def test_exhaustive_small_encodings(self):
        for defect, c in chains(10000, 4):
            description = encode(c, defect)
            self.assertLessEqual(len(description.segments), 2 * defect + 1)
            self.assertEqual(decode(description, max_bits=14), c.values[-1])

    def test_multiple_clipped_runs_and_a_saved_far_reference(self):
        def square(ops, n):
            for _ in range(n):
                i = len(ops)
                ops.append(("*", i, i))

        ops = [("+", 0, 0)]
        square(ops, 11)
        ops.append(("*", 12, 11))
        square(ops, 6)
        c = build(ops)
        d = encode(c, 1)
        self.assertEqual(len(d.segments), 1)
        self.assertGreaterEqual(d.segments[0].extra, 2)
        self.assertEqual(decode(d), c.values[-1])
        ops = [("+", 0, 0)]
        square(ops, 15)
        ops.append(("*", 16, 15))
        ops.append(("+", 17, 8))
        c = build(ops)
        d = encode(c, 2)
        self.assertTrue(any(seg.extra for seg in d.segments))
        self.assertIn(("saved", 0), d.segments[-1].reset)
        self.assertEqual(decode(d), c.values[-1])
        with self.assertRaises(OverflowError):
            decode(d, max_bits=2000)

    def test_fixed_defect_construction_vandermonde(self):
        for s in range(1, 5):
            for L in range(2 * s, 12):
                results = set()
                for k in range(s, L):
                    total = L - k - 1
                    for idx in itertools.combinations(range(k), s):
                        indices = tuple(reversed(idx))
                        for bars in itertools.combinations(range(1, total + 1), s - 1):
                            marks = (0, *bars)
                            gaps = tuple(b - a for a, b in zip(marks, marks[1:]))
                            tail = total - marks[-1]
                            row = nested_witness(k, indices, gaps, tail)
                            self.assertEqual((level(row[-1]), len(row) - 1), (L, L + s))
                            self.assertEqual(
                                nested_coordinates(row[-1], s), (k, indices, gaps, tail)
                            )
                            self.assertNotIn(row[-1], results)
                            results.add(row[-1])
                self.assertEqual(len(results), comb(L, 2 * s))

    def test_reset_loss_and_invalid_descriptions(self):
        for s in range(40):
            growth = Fraction(1, 2) + Fraction(2**s, 2 ** radius(s))
            self.assertLess(growth ** (s + 1), Fraction(1, 2**s))
        with self.assertRaises(ValueError):
            decode(Description(0, (("%", 0, 0),), ()))
        with self.assertRaises(ValueError):
            decode(Description(1, (), (Segment((), 2, None),)))
        with self.assertRaises(ValueError):
            decode(Description(1, (), (Segment((), 0, ("+", ("saved", 0), ("prefix", 0))),)))
