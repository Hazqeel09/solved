import unittest
from itertools import combinations_with_replacement
from math import isqrt

from checks.verify_two_small import verify
from solved.chains import chains, level
from solved.two_small_forms import blocks, gap_cutoff, square_run, two_small_chains


class TwoSmallTests(unittest.TestCase):
    def test_all_pairs(self):
        for cap in (1, 2, 3, 4, 5, 6, 15, 16, 17, 63, 64, 65, 255, 256, 257, 10**18):
            with self.subTest(cap=cap):
                result = verify(cap)
                if cap == 10**18:
                    self.assertEqual(result["chains"], 14116)
                    self.assertEqual(result["shortest_defect_two_endpoints"], 1935)

    def test_input(self):
        self.assertEqual(square_run(2, 1), ())
        self.assertEqual(square_run(2, 16), (4, 16))
        for head, cap in ((1, 100), (0, 2), (True, 4), (2, 0), (2, 4.0)):
            with self.assertRaises(ValueError):
                square_run(head, cap)
        for value in (0, -1, True, 3.0):
            with self.assertRaises(ValueError):
                list(two_small_chains(value))
        for args in [(0, 3, 2, 1), (3, 3, 2, 1), (3, 5, 1, 1), (3, 5, 2, -1), (3, 5, True, 1)]:
            with self.assertRaises(ValueError):
                gap_cutoff(*args)

    def test_exact_cutoff(self):
        for m in range(2, 39):
            for upper in range(m + 1, 2 * m + 1):
                for w in (2, m, m * m):
                    for bound in (0, 1, 4, 9):
                        expected = max(
                            (g for g in range(1, bound + 1) if upper ** (2**g) <= w * m ** (2**g)),
                            default=0,
                        )
                        self.assertEqual(gap_cutoff(m, upper, w, bound), expected)
        self.assertEqual(gap_cutoff(8, 16, 4, 10), 1)

    def test_event_recipes_before_deduplication(self):
        for cost, chain in chains(32, 2):
            if not cost or chain.values[-1] < 3:
                continue
            p = chain.values
            m, cap = p[-1], 2**256 - 1
            run = square_run(m, cap)
            upper = 1 << (1 << level(m))
            for small in (False, True):
                expected = set()
                for g in range(len(run) + 1):
                    seq = p + run[:g]
                    head = seq[-1]
                    for i, j in combinations_with_replacement(range(len(seq)), 2):
                        for op, v in (("+", seq[i] + seq[j]), ("*", seq[i] * seq[j])):
                            if (
                                head < v <= cap
                                and v != head**2
                                and (level(v) == level(head)) == small
                            ):
                                expected.add((g, v, op, i, j))
                actual = {
                    (b.gap, b.value, b.op, b.left, b.right)
                    for b in blocks(p, run, upper, cap, small)
                }
                self.assertEqual(actual, expected, (p, small))

    def test_explicit_three_nonsquare_sector(self):
        # Evaluate the specialized catalogue independently of the event classifier.
        cap = 2**512 - 1
        tower = [1, 2]
        for a in range(5):
            A = tower[-1]
            first = {A + x for x in tower if A + x < A * A} | {A * x for x in tower if 2 <= x < A}
            for B in first:
                p = tuple(tower + [B])
                run = square_run(B, cap)
                expected = set()
                if A >= 4:
                    expected.update((0, v) for v in first if v > B)
                    expected.update((0, B + w) for w in p if (A, B, w) != (4, 8, 8))
                    expected.update(
                        (0, B * w)
                        for w in tower
                        if 2 <= w <= isqrt(A) and (B, w) != (A * isqrt(A), isqrt(A))
                    )
                for g, H in enumerate(run, 1):
                    expected.update(
                        (g, H + w) for w in p + run[:g] if not (A == 2 and g == 1 and w == H)
                    )
                    expected.update(
                        (g, H * w)
                        for w in tower
                        if w >= 2
                        and not (
                            g == 1
                            and ((A == 2 and w == 2) or (A >= 4 and B == A * isqrt(A) and w == A))
                        )
                    )
                    for d in range(1, g + 1):
                        valid_sum = B - A in tower and (A >= 16 or (A == 4 and B in (5, 6)))
                        valid_product = any(B == A * (2 ** (2**b)) for b in range(a - 1))
                        if d >= 2 or valid_sum or valid_product:
                            expected.add((g, H * B ** (2 ** (g - d))))
                got = {(b.gap, b.value) for b in blocks(p, run, A * A, cap, True)}
                self.assertEqual(got, {pair for pair in expected if pair[1] <= cap}, (A, B))
            tower.append(A * A)
