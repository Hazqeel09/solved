import random
import unittest
from collections import deque
from itertools import product

from solved.helper_search import next_values, saturate, synthesize, terminal_menu


def shortest(seeds, targets, limit):
    queue = deque([(frozenset(seeds), 0)])
    seen = {frozenset(seeds)}
    while queue:
        available, cost = queue.popleft()
        if set(targets) <= available:
            return cost
        for a, b in product(available, repeat=2):
            values = [a + b, a * b, a - b]
            if a % b == 0:
                values.append(a // b)
            for value in values:
                if 1 <= value <= limit and value not in available:
                    state = available | {value}
                    if state not in seen:
                        seen.add(state)
                        queue.append((state, cost + 1))
    return None


class HelperSearchTests(unittest.TestCase):
    def test_against_full_instruction_search(self):
        rng = random.Random(225)
        for _ in range(180):
            limit = rng.randrange(3, 13)
            seeds = set(rng.sample(range(1, limit + 1), rng.randrange(1, 3)))
            targets = set(rng.sample(range(1, limit + 1), rng.randrange(1, min(limit, 4) + 1)))
            optimum = shortest(seeds, targets, limit)
            for h in range(3):
                tape = synthesize(seeds, targets, limit, h)
                feasible = optimum is not None and optimum <= len(targets - seeds) + h
                self.assertEqual(tape is not None, feasible, (seeds, targets, h))
                if tape is None:
                    continue
                self.assertEqual(len(tape), optimum)
                available = set(seeds)
                for v, op, a, b in tape:
                    self.assertTrue({a, b} <= available)
                    self.assertNotIn(v, available)
                    self.assertEqual(
                        v,
                        {
                            "+": lambda: a + b,
                            "-": lambda: a - b,
                            "*": lambda: a * b,
                            "/": lambda: a // b,
                        }[op](),
                    )
                    if op == "/":
                        self.assertEqual(a % b, 0)
                    self.assertTrue(1 <= v <= limit)
                    available.add(v)
                self.assertTrue(targets <= available)

    def test_target_saturation_and_new_shared_helper(self):
        self.assertEqual(len(synthesize((2, 3), (5, 6), 10, 0)), 2)
        self.assertEqual(len(synthesize((2, 2, 3), (5, 5, 6), 10, 0)), 2)
        self.assertIsNone(synthesize((1,), (15, 17), 256, 1))
        tape = synthesize((1,), (15, 17), 256, 3)
        self.assertEqual(len(tape), 5)
        self.assertEqual(synthesize((1,), (1,), 1, 0), ())
        self.assertEqual(synthesize((1,), (), 1, 0), ())

    def test_terminal_menu_against_all_forward_final_helpers(self):
        rng = random.Random(762)
        for _ in range(200):
            cap = rng.randrange(4, 35)
            seeds = frozenset(rng.sample(range(1, cap + 1), rng.randrange(1, 4)))
            targets = frozenset(rng.sample(range(1, cap + 1), rng.randrange(1, 4)))
            available, _ = saturate(seeds, targets, cap)
            if targets <= available:
                continue
            wanted = terminal_menu(available, targets, cap)
            for helper in next_values(available, cap):
                reached, _ = saturate(available | {helper}, targets, cap)
                if targets <= reached:
                    self.assertIn(helper, wanted)
            for h in range(3):
                left = synthesize(seeds, targets, cap, h, terminal_pruning=False)
                right = synthesize(seeds, targets, cap, h)
                self.assertEqual(
                    None if left is None else len(left), None if right is None else len(right)
                )
        self.assertIn(4, terminal_menu(frozenset({1, 2}), frozenset({16}), 16))
        self.assertIn(4, terminal_menu(frozenset({1, 2}), frozenset({8}), 8))

    def test_invalid(self):
        for args in [
            ((), (), 5, 0),
            ((1,), (6,), 5, 0),
            ((1,), (), 5, -1),
            ((True,), (), 5, 0),
            ((1, True), (), 5, 0),
        ]:
            with self.assertRaises(ValueError):
                synthesize(*args)
