import itertools
import unittest

from solved.growth_gap import envelope, first_visit_bound


def layers(seeds, steps):
    states = {frozenset(seeds)}
    for k in range(steps + 1):
        yield set().union(*states)
        if k == steps:
            return
        children = set(states)
        for state in states:
            for a, b in itertools.combinations_with_replacement(sorted(state), 2):
                for n in (a + b, a * b, b - a, b // a if b % a == 0 else 0):
                    if n > 0 and n not in state:
                        children.add(state | {n})
        states = children


class GrowthTests(unittest.TestCase):
    def test_distinct_top_two_on_complete_small_machines(self):
        for seeds in (c for d in (1, 2, 3) for c in itertools.combinations(range(1, 6), d)):
            for k, values in enumerate(layers(seeds, 3)):
                by_size = sorted(values, reverse=True)
                pair = tuple((by_size + [None, None])[:2])
                for cap in (5, 29, 999999999):
                    self.assertEqual(
                        envelope(seeds, k, cap),
                        tuple(None if v is None else min(v, cap + 1) for v in pair),
                    )

    def test_signed_tower_cluster_and_initial_visits(self):
        maxima = []
        for k, values in enumerate(layers((1,), 5)):
            maxima.append(max(values))
            if k >= 2:
                self.assertEqual(sorted(values)[-2], 3 ** (2 ** (k - 2)))
        self.assertEqual(first_visit_bound((1,), [255, 252, 240], 256), 7)
        self.assertEqual(first_visit_bound((1,), [255, 252, 240], 256, gaps=False), 6)
        self.assertEqual(first_visit_bound((1, 2), (1, 1, 2), 2), 0)
        self.assertEqual(envelope([7], 10**9, 1000), (1001, 1001))
        for a, k, n in (([], 2, 5), ([0], 1, 5), ([6], 1, 5), ([2], -1, 5), ([2], True, 5)):
            with self.assertRaises(ValueError):
                envelope(a, k, n)
