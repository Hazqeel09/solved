import unittest

from solved.chains import Chain, chains
from solved.fixed_defect import radius
from solved.normalized_mass import normalized


def instance(gap):
    r = [1, 2]
    steps = [("+", 0, 0)]

    def sq():
        i = len(r) - 1
        steps.append(("*", i, i))
        r.append(r[-1] * r[-1])

    for _ in range(5 + gap):
        sq()
    i = len(r) - 1
    steps.append(("+", i, 1))
    r.append(r[-1] + 2)
    for _ in range(2):
        sq()
    return Chain(tuple(r), tuple(steps))


class NormalizedTests(unittest.TestCase):
    def test_reconstruct_all_small_endpoints(self):
        for s, c in chains(6000, 3):
            mass = normalized(c, s)
            self.assertEqual(mass.restore(), c.values[-1])
            self.assertLessEqual(len(mass.atoms), s)
            self.assertTrue(all(v > 0 for v in mass.terms.values()))

    def test_control_ignores_gap_but_real_reset_scalar_changes(self):
        a, b = instance(5), instance(6)
        ma, mb = normalized(a, 1), normalized(b, 1)
        self.assertEqual(ma.terms, mb.terms)
        self.assertNotEqual(ma.atoms, mb.atoms)
        self.assertEqual(ma.restore(), a.values[-1])
        self.assertEqual(mb.restore(), b.values[-1])
        self.assertLess(b.values[-1], a.values[-1] ** 2)

    def test_far_multiplication_atom(self):
        q = radius(2)
        r = [1, 2]
        ops = [("+", 0, 0)]
        for _ in range(q + 1):
            j = len(r) - 1
            r.append(r[-1] ** 2)
            ops.append(("*", j, j))
        j = len(r) - 1
        r.append(r[-1] * 2)
        ops.append(("*", j, 1))
        c = Chain(tuple(r), tuple(ops))
        m = normalized(c, 2)
        self.assertTrue(any(kind == "mul" for kind, _, _ in m.atoms))
        self.assertEqual(m.restore(), r[-1])

    def test_square_plus_one_children_order_without_floats(self):
        for n in (2, 3, 5, 11, 29):
            last = None
            for j in range(1, 8):
                child = n ** (1 << j) + 1
                if last is not None:
                    self.assertLess(
                        child, last * last
                    )  # One extra write gives a strictly larger real witness defect.
                self.assertGreater(child, n ** (1 << j))
                last = child
