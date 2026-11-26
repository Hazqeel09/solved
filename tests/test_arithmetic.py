import unittest
from fractions import Fraction

from solved.arithmetic import (
    DomainError,
    binary_results,
    bounded_divisors,
    calculate,
    missing_operand,
)


class ArithmeticTests(unittest.TestCase):
    def test_all_bounded_results_and_inverses(self):
        for cap in range(1, 16):
            for a in range(1, cap + 1):
                for b in range(1, cap + 1):
                    oracle = set()
                    for x, y in ((a, b), (b, a)):
                        for op, value in (
                            ("+", x + y),
                            ("-", x - y),
                            ("*", x * y),
                            ("/", Fraction(x, y)),
                        ):
                            valid = value == int(value) and 1 <= value <= cap
                            if valid:
                                oracle.add(int(value))
                                self.assertEqual(calculate(op, x, y, cap), value)
                            else:
                                with self.assertRaises(DomainError):
                                    calculate(op, x, y, cap)
                    result = list(binary_results(a, b, cap))
                    self.assertEqual({v for v, _ in result}, oracle)
                    for v, recipe in result:
                        self.assertEqual(calculate(*recipe, cap), v)
            for target in range(1, cap + 1):
                for known in range(1, cap + 1):
                    oracle = {
                        x
                        for x in range(1, cap + 1)
                        if target in {v for v, _ in binary_results(x, known, cap)}
                    }
                    offered = missing_operand(target, known, cap)
                    self.assertEqual({v for v, _ in offered}, oracle)
                    for _, recipe in offered:
                        self.assertEqual(calculate(*recipe, cap), target)

    def test_reject_invalid_domain_and_operation(self):
        for a, b, cap in (
            (True, 1, 4),
            (1.0, 1, 4),
            (0, 1, 4),
            (1, -1, 4),
            (1, 5, 4),
            (1, 1, 0),
            (1, 1, True),
            (1, 1, 4.0),
        ):
            with self.assertRaises(DomainError):
                calculate("+", a, b, cap)
            with self.assertRaises(DomainError):
                list(binary_results(a, b, cap))
            with self.assertRaises(DomainError):
                missing_operand(a, b, cap)
        with self.assertRaises(DomainError):
            calculate("^", 2, 3, 10)
        self.assertEqual(calculate("*", 10**9, 10**9, 10**18), 10**18)
        with self.assertRaises(DomainError):
            calculate("+", 10**18, 1, 10**18)

    def test_divisor_boundaries(self):
        for n in range(1, 200):
            self.assertEqual(bounded_divisors(n), tuple(d for d in range(1, n + 1) if n % d == 0))
        self.assertEqual(bounded_divisors(999999937), (1, 999999937))
        self.assertEqual(len(bounded_divisors(10**18)), 361)
        for invalid in (True, False, 1.0, 0, -1, 10**18 + 1):
            with self.assertRaises(ValueError):
                bounded_divisors(invalid)
