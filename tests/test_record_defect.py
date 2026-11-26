import unittest

from solved.chains import level
from solved.record_defect import max_nonsquares, record_max


class RecordDefectTests(unittest.TestCase):
    def test_exact_boundary_and_attainment(self):
        self.assertEqual([max_nonsquares(s) for s in range(3)], [3, 7, 10])
        for small in range(8):
            b = max_nonsquares(small)
            upper = 4
            while True:
                old, head = upper - 2, upper - 1
                initial = level(head)
                for _ in range(b):
                    old, head = head, old * head
                if initial + b - level(head) == small:
                    break
                upper *= upper
                self.assertLess(upper.bit_length(), 1025)
            self.assertEqual(b - small, level(head) - initial)

    def test_four_op_overwrites(self):
        for seeds in ((2, 2), (2, 3), (4, 1), (1, 8), (7, 7), (2, 15), (15, 14)):
            cap = 128
            start = max(seeds)
            states = {(tuple(sorted(seeds)), start, 0, 0)}
            for _ in range(5):
                new = set()
                for regs, peak, b, s in states:
                    for a in regs:
                        for v in regs:
                            writes = {a + v, a * v, a - v}
                            if a % v == 0:
                                writes.add(a // v)
                            for result in writes:
                                if not 1 <= result <= cap:
                                    continue
                                top = max(peak, result)
                                ns = b + (result != peak * peak)
                                ss = s + (level(peak) == level(top))
                                self.assertLessEqual(
                                    ns, min(max_nonsquares(ss), level(cap) - level(start) + ss)
                                )
                                for kept in regs:
                                    new.add((tuple(sorted((kept, result))), top, ns, ss))
                states = new

    def test_exact_peak_with_arbitrary_seeds(self):
        # Keep both physical slots and the historical peak. Enumerate flat,
        # descending, inexact and repeated-operand possibilities independently.
        for seeds in ((1, 3), (1, 16), (2, 15), (3, 9), (5, 6), (3, 3), (7, 15)):
            states = {(seeds, max(seeds), 0, 0)}
            for _ in range(4):
                seen = {}
                following = set()
                for regs, peak, b, d in states:
                    seen[b, d] = max(seen.get((b, d), 0), peak)
                    for a in regs:
                        for z in regs:
                            values = {a + z, a * z, a - z}
                            if a % z == 0:
                                values.add(a // z)
                            for v in values:
                                if v > 0:
                                    square = v == peak * peak
                                    for keep in regs:
                                        following.add(
                                            (
                                                tuple(sorted((keep, v))),
                                                max(peak, v),
                                                b + (not square),
                                                d + square,
                                            )
                                        )
                for (b, d), peak in seen.items():
                    self.assertEqual(record_max(seeds, b, d), peak, (seeds, b, d))
                    self.assertEqual(record_max(seeds, b, d, ceiling=37), min(37, peak))
                states = following
        self.assertEqual(record_max((1, 16), 2, 1), 16**5)
        self.assertEqual(record_max((3, 9), 2, 1), 9**5)
        self.assertEqual(record_max((7, 15), 10**6, 3, ceiling=99), 99)

    def test_fixed_bank_input_contract(self):
        for seeds, b, d, cap in [
            ((), 1, 1, None),
            ((2, 2), 1, 1, None),
            ((4, False), 1, 1, None),
            ((3,), -1, 1, None),
            ((3,), 1, True, None),
            ((4,), 0, 0, 0),
        ]:
            with self.assertRaises(ValueError):
                record_max(seeds, b, d, ceiling=cap)

    def test_invalid_counts(self):
        for bad in (True, 3.0, -1, None):
            with self.assertRaises(ValueError):
                max_nonsquares(bad)
