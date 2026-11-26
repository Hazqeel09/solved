import itertools
import unittest

from solved.registers import minimum_registers


def possible(seeds, rules, keep, slots):
    if slots < len(seeds):
        return False
    states = {(tuple(seeds) + (None,) * (slots - len(seeds)), frozenset())}
    for _ in rules:
        next_states = set()
        for cells, done in states:
            for out, (a, b) in rules.items():
                if out in done or a not in cells or b not in cells:
                    continue
                for i in range(slots):
                    next_states.add((cells[:i] + (out,) + cells[i + 1 :], done | {out}))
        states = next_states
    return any(set(keep) <= set(cells) for cells, _ in states)


class PebblingTests(unittest.TestCase):
    def test_read_then_overwrite_and_visit_only(self):
        self.assertEqual(minimum_registers((2, 3), {5: (2, 3), 6: (2, 3)}), 3)
        self.assertEqual(minimum_registers((2,), {4: (2, 2), 16: (4, 4)}), 1)
        self.assertEqual(minimum_registers((2,), {4: (2, 2), 16: (4, 4)}, (2, 4, 16)), 3)
        with self.assertRaises(ValueError):
            minimum_registers((1,), {2: (1, 3), 3: (1, 2)})
        with self.assertRaises(ValueError):
            minimum_registers((1,), {2: (1, 7)})
        self.assertEqual(minimum_registers((), {}), 0)

    def test_every_three_node_dag_on_two_inputs(self):
        for ab, cd, ef in itertools.product(
            *(list(itertools.combinations_with_replacement(range(n), 2)) for n in (2, 3, 4))
        ):
            rules = {2: ab, 3: cd, 4: ef}
            for keep in ((), (0,), (2, 4)):
                r = minimum_registers((0, 1), rules, keep)
                self.assertTrue(possible((0, 1), rules, keep, r))
                self.assertFalse(possible((0, 1), rules, keep, r - 1))
