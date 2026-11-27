import json
import random
import unittest
from itertools import product

from scripts.check_catalogue import ROOT
from solved import lean_icg as li
from solved.icg_energy import direct_energy

RECORDS = json.loads((ROOT / "checks" / "expected" / "icg-families.json").read_text())
EVEN = {
    (r["order"][0][1], r["order"][1][1]): r
    for r in RECORDS
    if r["result"]["kind"] == "one-symbolic" and r["order"][0][0] == 2
}


def divisors_of(a, b, p, mask):
    B = b + 1
    return [2 ** (k // B) * p ** (k % B) for k, bit in enumerate(mask) if bit]


class ListSemantics(unittest.TestCase):
    """The Python operations mirror the Lean list definitions, including lengths."""

    def test_mul_lengths(self):
        self.assertEqual(li.pmul([], [1, 2]), [])
        self.assertEqual(li.pmul([5], []), [0])
        self.assertEqual(li.pmul([5, 7], []), [0, 0])
        self.assertEqual(li.pmul([1, 2], [3, 4]), [3, 10, 8])

    def test_shift(self):
        rng = random.Random(1)
        for _ in range(200):
            p = [rng.randint(-9, 9) for _ in range(rng.randint(0, 7))]
            k = rng.randint(0, 4)
            s = li.shift(k, p)
            self.assertEqual(len(s), len(p))
            for x in range(-3, 4):
                self.assertEqual(li.peval(s, x), li.peval(p, x + k))

    def test_add_pads(self):
        self.assertEqual(li.padd([1], [2, 3]), [3, 3])
        self.assertEqual(li.padd([], []), [])


class CellModel(unittest.TestCase):
    """The cell polynomials reproduce the definitional energy E(n, D) = sum phi |sum c|."""

    def test_against_definition(self):
        rng = random.Random(2)
        for a, b in [(1, 1), (1, 2), (2, 1), (2, 2), (3, 1), (1, 3)]:
            cells = (a + 1) * (b + 1) - 1
            for p in (3, 5, 7, 11):
                n = 2**a * p**b
                masks = list(product([False, True], repeat=cells))
                if len(masks) > 64:
                    masks = rng.sample(masks, 64)
                for mask in masks:
                    self.assertEqual(
                        li.model_energy(a, b, p, mask),
                        direct_energy(n, divisors_of(a, b, p, mask)),
                        (a, b, p, mask),
                    )


class Certificates(unittest.TestCase):
    def test_maximal_at_small_primes(self):
        """E(p) is the maximum over all masks, attained exactly by the maximisers, for p >= p0."""
        for (a, b), record in EVEN.items():
            cells = (a + 1) * (b + 1) - 1
            if cells > 11:
                continue
            cert = li.family_certificate(record)
            for p in (5, 7, 11, 13):
                if p < cert["p0"]:
                    continue
                values = {
                    mask: li.model_energy(a, b, p, mask)
                    for mask in product([False, True], repeat=cells)
                }
                top = max(values.values())
                self.assertEqual(top, li.peval(cert["energy"], p), (a, b, p))
                winners = sorted(mask for mask, v in values.items() if v == top)
                self.assertEqual(winners, sorted(tuple(mk) for mk in cert["masks"]), (a, b, p))

    def test_width_is_minimal(self):
        for (a, b), record in EVEN.items():
            if (a + 1) * (b + 1) > 10:
                continue
            cert = li.family_certificate(record)
            m = (a + 1) * (b + 1)
            total = sum(
                abs(c) for k in cert["order"] for f in li.cell_table(a, b, cert["p0"], k) for c in f
            )
            tail = sum(abs(c) for c in li.shift(cert["p0"], cert["energy"]))
            need = 4 * m * total + tail
            self.assertLess(need, 2 ** (cert["w"] - 1))
            self.assertGreaterEqual(need, 2 ** (cert["w"] - 2))
            self.assertEqual(cert["D"], b + 1)

    def test_small_primes_against_definition(self):
        """The fixed-prime data agree with an exhaustive search using the definitional energy."""
        certs = li.small_prime_certificates(EVEN[(3, 1)])
        self.assertEqual([c["p"] for c in certs], [3])
        for cert in certs:
            n = 2 ** cert["a"] * cert["p"] ** cert["b"]
            proper = [d for d in range(1, n) if n % d == 0]
            values = {}
            for code in range(1 << len(proper)):
                subset = tuple(d for i, d in enumerate(proper) if code >> i & 1)
                values[subset] = direct_energy(n, subset)
            top = max(values.values())
            self.assertEqual(top, cert["energy"])
            winners = sorted(tuple(sorted(s)) for s, v in values.items() if v == top)
            claimed = sorted(
                tuple(sorted(2**c * cert["p"] ** e for c, e in cs)) for cs in cert["cells"]
            )
            self.assertEqual(winners, claimed)

    def test_rejects_wrong_energy(self):
        record = json.loads(json.dumps(EVEN[(1, 1)]))
        record["result"]["energy"][0][2] += 1
        with self.assertRaises(ValueError):
            li.family_certificate(record)

    def test_rejects_wrong_maximiser(self):
        record = json.loads(json.dumps(EVEN[(1, 2)]))
        record["result"]["maximisers"] = record["result"]["maximisers"][:1]
        with self.assertRaises(ValueError):
            li.family_certificate(record)

    def test_rejects_odd_orders(self):
        odd = next(r for r in RECORDS if r["order"][0][0] == 3)
        with self.assertRaises(ValueError):
            li.family_certificate(odd)


class Rendering(unittest.TestCase):
    def test_polynomial_text(self):
        self.assertEqual(li._real_poly([-2, 4]), "-2 + 4 * (p : ℝ)")
        self.assertEqual(li._real_poly([0, 1, -1]), "(p : ℝ) - (p : ℝ) ^ 2")
        self.assertEqual(li._real_poly([3, 0, 2]), "3 + 2 * (p : ℝ) ^ 2")

    def test_committed_files_are_current(self):
        formal = ROOT / "formal"
        self.assertEqual((formal / "Formal/ICG/EvenFamilies.lean").read_text(), li.render(RECORDS))
        self.assertEqual(
            (formal / "FormalTests/Axioms.lean").read_text(), li.render_axioms(RECORDS)
        )

    def test_axiom_audit_lists_every_family(self):
        text = li.render_axioms(RECORDS)
        for a, b in EVEN:
            self.assertIn(f"#print axioms Solved.ICG.Families.energy_{a}_{b}\n", text)


if __name__ == "__main__":
    unittest.main()
