import json
import random
import shutil
import tempfile
import unittest
from itertools import product
from pathlib import Path

from scripts.check_catalogue import REGISTRIES, ROOT, validate_mathlib_registry
from solved import lean_icg as li
from solved.icg_energy import direct_energy


def _prod(values):
    out = 1
    for v in values:
        out *= v
    return out


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


class MultiBridge(unittest.TestCase):
    """The statement of the k-prime bridge, against the definitional energy formula."""

    def test_against_definition(self):
        rng = random.Random(3)
        cases = [
            ((2, 3), (1, 1)),
            ((2, 5), (2, 1)),
            ((3, 7), (1, 2)),
            ((2, 3, 5), (1, 1, 1)),
            ((2, 3, 5), (2, 1, 1)),
            ((3, 5, 7), (1, 1, 1)),
            ((2, 3, 5, 7), (1, 1, 1, 1)),
            ((2, 7, 11), (1, 2, 1)),
        ]
        for primes, exponents in cases:
            n = 1
            for r, a in zip(primes, exponents):
                n *= r**a
            proper = [d for d in range(1, n) if n % d == 0]
            subsets = [()] + [tuple(d for d in proper if rng.random() < 0.5) for _ in range(40)]
            for subset in subsets:
                self.assertEqual(
                    li.multi_energy(primes, exponents, set(subset)),
                    direct_energy(n, subset),
                    (primes, exponents, subset),
                )


class MultiCertificates(unittest.TestCase):
    """Region certificate data against exhaustive search with the definitional energy."""

    PAIRS = {"lt": [(3, 5), (5, 11), (7, 13)], "gt": [(5, 3), (11, 5), (13, 7)]}

    def test_regions_against_definition(self):
        for record in RECORDS:
            if record["result"]["kind"] != "two-symbolic":
                continue
            fixed = [r for r, _ in record["order"] if isinstance(r, int)]
            for region, pairs in self.PAIRS.items():
                key = "p<q" if region == "lt" else "p>q"
                if record["result"][key]["certificate"] != "exact":
                    continue
                cert = li.multi_certificate(record, region)
                for p, q in pairs:
                    if min(p, q) < cert["p0"] or p in fixed or q in fixed:
                        continue
                    primes = [p if r == "p" else q if r == "q" else r for r, _ in record["order"]]
                    exps = [e for _, e in record["order"]]
                    n = 1
                    for r, e in zip(primes, exps):
                        n *= r**e
                    proper = [d for d in range(1, n) if n % d == 0]
                    if len(proper) > 11:
                        sets = [()]  # exhaustive only for small orders; maximisers below
                    else:
                        sets = [
                            tuple(d for i, d in enumerate(proper) if code >> i & 1)
                            for code in range(1 << len(proper))
                        ]
                    energy = sum(c * p**i * q**j for i, j, c in record["result"][key]["energy"])
                    claimed = set()
                    for cells in cert["cells"]:
                        div = 1
                        dset = []
                        for c in cells:
                            div = 1
                            for r, ci in zip(primes, c):
                                div *= r**ci
                            dset.append(div)
                        claimed.add(tuple(sorted(dset)))
                    for divisors in claimed:
                        self.assertEqual(
                            direct_energy(n, divisors), energy, (record["order"], p, q)
                        )
                    if len(sets) > 1:
                        values = {tuple(sorted(sub)): direct_energy(n, sub) for sub in sets}
                        top = max(values.values())
                        self.assertEqual(top, energy, (record["order"], p, q))
                        winners = {sub for sub, v in values.items() if v == top}
                        self.assertEqual(winners, claimed, (record["order"], p, q))

    def test_candidate_regions_exhaustively(self):
        """certifyMax data: candidates attain their energies, every other set is below one."""
        found = 0
        for record in RECORDS:
            result = record["result"]
            if result["kind"] != "two-symbolic" or result["p>q"]["certificate"] == "exact":
                continue
            found += 1
            cert = li.max_certificate(record)
            exps = [e for _, e in record["order"]]
            self.assertEqual(len(cert["masks"]), len(cert["Es"]))
            for p, q in [(5, 3), (7, 3), (7, 5), (11, 3), (13, 11), (23, 3)]:
                if q < cert["p0"]:
                    continue
                primes = [p if r == "p" else q if r == "q" else r for r, _ in record["order"]]
                full = list(product(*(range(a + 1) for a in exps)))
                box = full[:-1]

                def pw(c, primes=primes):
                    value = 1
                    for r, e in zip(primes, c):
                        value *= r**e
                    return value

                tent = [
                    [
                        _prod(
                            li.peval(li.tent_p(a, ui, ci), r)
                            for r, a, ui, ci in zip(primes, exps, u, c)
                        )
                        for c in box
                    ]
                    for u in full
                ]
                values = {}
                for code in range(1 << len(box)):
                    chosen = [i for i in range(len(box)) if code >> i & 1]
                    values[frozenset(box[i] for i in chosen)] = sum(
                        abs(sum(row[i] for i in chosen)) for row in tent
                    )
                energies = [
                    sum(c * p**i * q**j for i, row in enumerate(E) for j, c in enumerate(row))
                    for E in cert["Es"]
                ]
                cand = [frozenset(map(tuple, cs)) for cs in cert["cells"]]
                self.assertEqual(len(set(cand)), len(cand))
                for cells, energy in zip(cand, energies):
                    self.assertEqual(values[cells], energy, (record["order"], p, q))
                    divisors = [pw(c) for c in cells]
                    self.assertEqual(li.multi_energy(primes, exps, divisors), energy)
                    self.assertEqual(direct_energy(pw(full[-1]), divisors), energy)
                for cells, value in values.items():
                    if cells not in cand:
                        self.assertLess(value, max(energies), (record["order"], p, q, cells))
        self.assertEqual(found, 2)

    def test_ratio_2p2q(self):
        """MultiRatio: E(A) - E(B) = 2(5p^2 - 6pq + 9q - 8), never zero at primes 3 <= q < p."""
        record = next(r for r in RECORDS if r["order"] == [[2, 1], ["p", 2], ["q", 1]])
        cert = li.max_certificate(record)
        primes = [n for n in range(3, 400) if all(n % d for d in range(2, int(n**0.5) + 1))]
        seen = set()
        for q in primes:
            for p in primes:
                if p <= q:
                    continue
                ea, eb = (
                    sum(c * p**i * q**j for i, row in enumerate(E) for j, c in enumerate(row))
                    for E in cert["Es"]
                )
                d = 5 * p * p - 6 * p * q + 9 * q - 8
                self.assertEqual(ea - eb, 2 * d)
                self.assertNotEqual(d, 0)
                seen.add(d > 0)
        self.assertEqual(seen, {True, False})  # both theorems have instances
        zeros = [
            (p, q)
            for p in range(1, 200)
            for q in range(1, 200)
            if 5 * p * p - 6 * p * q + 9 * q - 8 == 0
        ]
        # 2p - 3 divides 13: p in {1, 2, 8}, all excluded by p > q >= 3 and primality
        self.assertEqual(zeros, [(1, 1), (2, 4), (8, 8)])

    def test_ratio_2p3q(self):
        """MultiRatio: E_1 = E_3 = E_4 and E_1 - E_2 = 2(7p^3 - 9p^2q + 18pq - 16p - 9q + 8)."""
        record = next(r for r in RECORDS if r["order"] == [[2, 1], ["p", 3], ["q", 1]])
        cert = li.max_certificate(record)
        e1, e2, e3, e4 = cert["Es"]
        self.assertEqual(e1, e3)
        self.assertEqual(e1, e4)
        self.assertNotEqual(e1, e2)
        primes = [n for n in range(3, 400) if all(n % d for d in range(2, int(n**0.5) + 1))]
        seen = set()
        for q in primes:
            for p in primes:
                if p <= q:
                    continue
                ea, eb = (
                    sum(c * p**i * q**j for i, row in enumerate(E) for j, c in enumerate(row))
                    for E in (e1, e2)
                )
                d = 7 * p**3 - 9 * p * p * q + 18 * p * q - 16 * p - 9 * q + 8
                self.assertEqual(ea - eb, 2 * d)
                self.assertNotEqual(d, 0)
                seen.add(d > 0)
        self.assertEqual(seen, {True, False})
        # (p - 1)(9q(p - 1) - 7p^2 - 7p + 9) = -1 has no solution with p - 1 >= 3
        zeros = [
            (p, q)
            for p in range(4, 300)
            for q in range(0, 300)
            if 7 * p**3 - 9 * p * p * q + 18 * p * q - 16 * p - 9 * q + 8 == 0
        ]
        self.assertEqual(zeros, [])
        self.assertEqual([p for p in range(2, 50) if 13 % (2 * p - 3) == 0], [2, 8])

    def test_masks_match_cells(self):
        record = next(r for r in RECORDS if r["order"] == [[2, 1], ["p", 1], ["q", 1]])
        cert = li.multi_certificate(record, "lt")
        for mask, cells in zip(cert["masks"], cert["cells"]):
            chosen = {li.mixed_enc(cert["shape"].a, c) for c in cells}
            self.assertEqual({k for k, bit in enumerate(mask) if bit}, chosen)
            self.assertNotIn(cert["shape"].size - 1, chosen)


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
        self.assertEqual((ROOT / REGISTRIES[1]).read_text(), li.render_registry(RECORDS))
        self.assertEqual(
            (formal / "Formal/ICG/MultiFamilies.lean").read_text(), li.render_multi(RECORDS)
        )
        manuscript = (ROOT / "results/icg-energy-even-orders/PROOF.md").read_text()
        self.assertEqual(manuscript, li.update_table(manuscript, RECORDS))
        multi = (ROOT / "results/icg-energy-two-symbolic-primes/PROOF.md").read_text()
        self.assertEqual(multi, li.update_multi_table(multi, RECORDS))

    def test_axiom_audit_lists_every_family(self):
        text = li.render_axioms(RECORDS)
        for a, b in EVEN:
            self.assertIn(f"#print axioms Solved.ICG.Families.energy_{a}_{b}\n", text)


class Registry(unittest.TestCase):
    """The repository check rejects registries the Lean audit would not back."""

    def copy(self):
        tmp = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, tmp)
        registry = json.loads((ROOT / REGISTRIES[1]).read_text())
        for name in [REGISTRIES[1], registry["audit"]] + [m["file"] for m in registry["modules"]]:
            (tmp / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / name, tmp / name)
        return tmp, registry

    def test_current_registry_passes(self):
        tmp, _ = self.copy()
        validate_mathlib_registry(tmp)

    def test_rejects_missing_audit_line(self):
        tmp, registry = self.copy()
        audit = tmp / registry["audit"]
        name = registry["modules"][-1]["theorems"][0]
        audit.write_text(audit.read_text().replace(f"#print axioms {name}\n", ""))
        with self.assertRaises(ValueError):
            validate_mathlib_registry(tmp)

    def test_rejects_weakened_guard(self):
        tmp, registry = self.copy()
        audit = tmp / registry["audit"]
        audit.write_text(audit.read_text().replace("Quot.sound]", "Quot.sound, sorryAx]", 1))
        with self.assertRaises(ValueError):
            validate_mathlib_registry(tmp)

    def test_rejects_sorry_in_code_but_not_in_comments(self):
        tmp, registry = self.copy()
        module = tmp / registry["modules"][0]["file"]
        module.write_text(module.read_text() + "\n-- a remark about sorry\n")
        validate_mathlib_registry(tmp)
        module.write_text(module.read_text() + "\ntheorem bad : False := sorry\n")
        with self.assertRaises(ValueError):
            validate_mathlib_registry(tmp)

    def test_rejects_undeclared_theorem(self):
        tmp, registry = self.copy()
        registry["modules"][0]["theorems"].append("Solved.ICG.no_such_theorem")
        (tmp / REGISTRIES[1]).write_text(json.dumps(registry))
        with self.assertRaises(ValueError):
            validate_mathlib_registry(tmp)


if __name__ == "__main__":
    unittest.main()
