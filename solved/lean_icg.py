"""Certificate data for the Lean theorems on maximal energy of ICG(2^a p^b, S).

The Lean checker ``Solved.ICG.certifyP`` (formal/Formal/ICG/EvenPacked.lean) needs, for each
order 2^a p^b, the energy polynomial E(p), the maximising masks, an order in which to decide
the cells, a packed field width and the number of coefficients per polynomial. Its soundness
does not depend on any of these choices: a wrong value makes the kernel reject the
certificate. This module computes them from checks/expected/icg-families.json and writes
formal/Formal/ICG/EvenFamilies.lean.

Polynomials are coefficient lists, lowest degree first, with the same list operations as
formal/Formal/Cert/UPoly.lean and formal/Formal/ICG/LocalPoly.lean, so lengths agree with the
kernel's lists.
"""

import json
from pathlib import Path

# --- integer polynomials as in Formal/Cert/UPoly.lean -------------------------------------


def padd(p, q):
    """UPoly.add: coefficientwise sum, the shorter list padded with zeros."""
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def pscale(c, p):
    return [c * x for x in p]


def pmul(p, q):
    """UPoly.mul: mul [] q = [], mul (a :: p) q = add (scale a q) (0 :: mul p q)."""
    if not p:
        return []
    return padd(pscale(p[0], q), [0] + pmul(p[1:], q))


def peval(p, x):
    out = 0
    for c in reversed(p):
        out = c + x * out
    return out


def shift1(p):
    """UPoly.shift1: eval (shift1 p) x = eval p (x + 1)."""
    if not p:
        return []
    s = shift1(p[1:])
    return padd([p[0]], padd(s, [0] + s))


def shift(k, p):
    for _ in range(k):
        p = shift1(p)
    return p


def neg(p):
    return [-c for c in p]


def nonneg(p):
    return all(c >= 0 for c in p)


def nonpos(p):
    return all(c <= 0 for c in p)


# --- local Ramanujan factors as in Formal/ICG/LocalPoly.lean ---------------------------------


def _mono(k, p):
    return [0] * k + p


def phi_p(e):
    return [1] if e == 0 else _mono(e - 1, [-1, 1])


def ram_p(k, u):
    if k == 0:
        return [1]
    if k <= u:
        return phi_p(k)
    if k == u + 1:
        return _mono(u, [-1])
    return []


def tent_p(m, u, j):
    return pmul(phi_p(max(m - u, 0)), ram_p(max(m - j, 0), u))


def cell_p(a, b, k, e):
    """cellP: contribution of cell k = i(b+1)+l to entry e = u(b+1)+v, a polynomial in p."""
    B = b + 1
    return pscale(peval(tent_p(a, e // B, k // B), 2), tent_p(b, e % B, k % B))


def cell_table(a, b, p0, k):
    """cellTable: the contributions of cell k to every entry, in x = p - p0."""
    return [shift(p0, cell_p(a, b, k, e)) for e in range((a + 1) * (b + 1))]


def multi_energy(primes, exponents, divisors):
    """The right side of `Solved.ICG.Multi.energy_icgAdj_multi` at concrete primes.

    sum over classes u of |sum over cells c with prod r^c in S of prod_i Tent(r_i, a_i, u_i, c_i)|,
    both over the exponent box; `Tent` is `tent_p` evaluated at the prime.
    """
    from itertools import product as cartesian

    box = list(cartesian(*(range(a + 1) for a in exponents)))
    chosen = []
    for c in box:
        value = 1
        for r, e in zip(primes, c):
            value *= r**e
        if value in divisors:
            chosen.append(c)
    total = 0
    for u in box:
        entry = 0
        for c in chosen:
            term = 1
            for r, a, ui, ci in zip(primes, exponents, u, c):
                term *= peval(tent_p(a, ui, ci), r)
            entry += term
        total += abs(entry)
    return total


def model_energy(a, b, p, mask):
    """sum_e |sum_{k in mask} cellP k e (p)|: the energy of ICG(2^a p^b, S) for S's mask."""
    m = (a + 1) * (b + 1)
    return sum(
        abs(sum(peval(cell_p(a, b, k, e), p) for k, bit in enumerate(mask) if bit))
        for e in range(m)
    )


# --- certificate data -----------------------------------------------------------------------


def masks_of(maximisers, b, cells):
    """Masks of length `cells` from lists of exponent pairs (i, j) for the divisors 2^i p^j."""
    out = []
    for divisor_set in maximisers:
        mask = [False] * cells
        for i, j in divisor_set:
            mask[i * (b + 1) + j] = True
        out.append(mask)
    return out


def energy_polynomial(a, b, p0, mask):
    """E(p) for a maximiser whose shifted entries have certified signs."""
    m = (a + 1) * (b + 1)
    entries = [[] for _ in range(m)]
    for k, bit in enumerate(mask):
        if bit:
            entries = [padd(f, cell_p(a, b, k, e)) for e, f in enumerate(entries)]
    total = []
    for f in entries:
        shifted = shift(p0, f)
        if not (nonneg(shifted) or nonpos(shifted)):
            raise ValueError("maximiser entry without a certified sign")
        total = padd(total, f if nonneg(shifted) else neg(f))
    while total and total[-1] == 0:
        total.pop()
    return total


def search_nodes(a, b, p0, target_mask, order):
    """Nodes visited by the interval branch and bound of `bnbP`, and its unpruned leaves.

    The node test is the one proved in Formal/Cert/PackedBB.lean: with accumulated table a and
    undecided cells R, the bound has coefficients sum_e (-a - lo + max(2a + S, 0)).
    """
    m = (a + 1) * (b + 1)
    tables = {k: cell_table(a, b, p0, k) for k in order}
    target = shift(p0, energy_polynomial(a, b, p0, target_mask))
    suffix_s = [[[] for _ in range(m)]]
    suffix_lo = [[[] for _ in range(m)]]
    for k in reversed(order):
        suffix_s.insert(0, [padd(s, t) for s, t in zip(suffix_s[0], tables[k])])
        suffix_lo.insert(
            0, [padd(lo, [min(c, 0) for c in t]) for lo, t in zip(suffix_lo[0], tables[k])]
        )
    nodes, leaves = 0, []

    def bound(depth, acc):
        out = []
        for e in range(m):
            a_e, s_e, lo_e = acc[e], suffix_s[depth][e], suffix_lo[depth][e]
            n = max(len(a_e), len(s_e), len(lo_e))
            get = lambda f, i: f[i] if i < len(f) else 0  # noqa: E731
            out = padd(
                out,
                [
                    -get(a_e, i) - get(lo_e, i) + max(2 * get(a_e, i) + get(s_e, i), 0)
                    for i in range(n)
                ],
            )
        return out

    def passes(bnd):
        diff = padd(target, neg(bnd))
        return bool(diff) and diff[0] > 0 and nonneg(diff[1:])

    def go(depth, path, acc):
        nonlocal nodes
        nodes += 1
        if passes(bound(depth, acc)):
            return
        if depth == len(order):
            leaves.append(path)
            return
        k = order[depth]
        go(depth + 1, path, acc)
        go(depth + 1, path | (1 << k), [padd(x, y) for x, y in zip(acc, tables[k])])

    go(0, 0, [[] for _ in range(m)])
    return nodes, leaves


def _orders(a, b):
    cells = list(range((a + 1) * (b + 1) - 1))
    B = b + 1
    return {
        "natural": cells,
        "reverse": cells[::-1],
        "exponent-of-p first": sorted(cells, key=lambda k: (k % B, k // B)),
        "exponent-of-p last": sorted(cells, key=lambda k: (-(k % B), -(k // B))),
    }


def field_width(a, b, p0, energy, order):
    """Smallest w with 4 m B + T < 2^(w-1), the size condition of `certifyP`."""
    m = (a + 1) * (b + 1)
    total = sum(abs(c) for k in order for f in cell_table(a, b, p0, k) for c in f)
    tail = sum(abs(c) for c in shift(p0, energy))
    return (4 * m * total + tail).bit_length() + 1


def family_certificate(record):
    """Lean certificate data for one even family of checks/expected/icg-families.json."""
    (two, a), (_, b) = record["order"]
    result = record["result"]
    if two != 2 or result["kind"] != "one-symbolic":
        raise ValueError("not an order 2^a p^b")
    cells = (a + 1) * (b + 1) - 1
    p0 = result["certified_from"]
    masks = masks_of(result["maximisers"], b, cells)
    energy = energy_polynomial(a, b, p0, masks[0])
    stored = [0] * (1 + max(t[0] for t in result["energy"]))
    for degree, q_degree, c in result["energy"]:
        if q_degree != 0:
            raise ValueError("unexpected q-degree")
        stored[degree] += c
    if energy != stored:
        raise ValueError("energy polynomial disagrees with the stored certificate")
    expected = sorted(sum(1 << k for k, bit in enumerate(mk) if bit) for mk in masks)
    best = None
    for name, order in _orders(a, b).items():
        nodes, leaves = search_nodes(a, b, p0, masks[0], order)
        if sorted(leaves) != expected:
            raise ValueError("unpruned leaves differ from the maximisers")
        if best is None or nodes < best[0]:
            best = (nodes, name, order)
    nodes, name, order = best
    lengths = {len(f) for k in order for f in cell_table(a, b, p0, k)}
    return {
        "a": a,
        "b": b,
        "p0": p0,
        "w": field_width(a, b, p0, energy, order),
        "D": max(lengths | {len(shift(p0, energy))}),
        "energy": energy,
        "order": order,
        "order_name": name,
        "nodes": nodes,
        "masks": masks,
        "cells": [[(k // (b + 1), k % (b + 1)) for k, bit in enumerate(mk) if bit] for mk in masks],
    }


def small_prime_certificates(record):
    """Certificate data for the exceptional primes below p0, by exhaustive enumeration."""
    (_, a), (_, b) = record["order"]
    result = record["result"]
    cells = (a + 1) * (b + 1) - 1
    out = []
    for prime, maximisers in sorted(result["small_primes"].items(), key=lambda kv: int(kv[0])):
        p = int(prime)
        masks = masks_of(maximisers, b, cells)
        values = {}
        for code in range(1 << cells):
            mask = [bool(code >> k & 1) for k in range(cells)]
            values[code] = model_energy(a, b, p, mask)
        top = max(values.values())
        winners = sorted(c for c, v in values.items() if v == top)
        if winners != sorted(sum(1 << k for k, bit in enumerate(mk) if bit) for mk in masks):
            raise ValueError("stored small-prime maximisers are not the argmax")
        out.append(
            {
                "a": a,
                "b": b,
                "p": p,
                "energy": top,
                "masks": masks,
                "cells": [
                    [(k // (b + 1), k % (b + 1)) for k, bit in enumerate(mk) if bit] for mk in masks
                ],
            }
        )
    return out


# --- Lean rendering ---------------------------------------------------------------------------


def _lean_list(items):
    return "[" + ", ".join(items) + "]"


def _lean_bools(mask):
    return _lean_list("true" if bit else "false" for bit in mask)


def _real_poly(coeffs):
    terms = []
    for i, c in enumerate(coeffs):
        if c == 0:
            continue
        mono = "" if i == 0 else "(p : ℝ)" if i == 1 else f"(p : ℝ) ^ {i}"
        body = str(abs(c)) if i == 0 else mono if abs(c) == 1 else f"{abs(c)} * {mono}"
        terms.append(("-" if c < 0 else "+", body))
    out = ("-" if terms[0][0] == "-" else "") + terms[0][1]
    for sign, body in terms[1:]:
        out += f" {sign} {body}"
    return out


def _divisors(cells):
    return ", ".join(f"2 ^ {c} * p ^ {e}" for c, e in cells)


HEADER = """\
import Formal.ICG.EvenAt

/-!
# Maximal energy of `ICG(2^a p^b, S)`: kernel-checked families

Generated by `python -m scripts.lean_icg_families` from `checks/expected/icg-families.json`;
do not edit by hand. For each family the kernel evaluates `certifyP` (`decide +kernel`, no
`native_decide`), and `energy_le_of_certifyP` turns it into a statement about the energy of the
integral circulant graph `ICG(2^a p^b, S)` for every prime `p ≥ p₀` and every set `S` of proper
divisors, including the empty set. Primes below `p₀` with different maximisers are covered by
`certifyAt` (`energy_le_of_certifyAt`).

For the literature on these orders see `results/icg-energy-exceptional-orders/PROOF.md`; whether
a family is new is assessed there, not here.
-/

namespace Solved.ICG.Families

open Solved.Cert Solved.ICG

"""


def render_family(cert):
    a, b, p0 = cert["a"], cert["b"], cert["p0"]
    energy = _lean_list(map(str, cert["energy"]))
    expr = _real_poly(cert["energy"])
    masks, cells = cert["masks"], cert["cells"]
    graph = f"ICGBridge.energy (ICGBridge.icgAdj (2 ^ {a} * p ^ {b}) S) (ICGBridge.icgAdj_isHermitian _ _)"
    sets = " ∨ ".join(f"S = {{{_divisors(cs)}}}" for cs in cells)
    docsets = ", ".join("`{" + ", ".join(f"2^{c} p^{e}" for c, e in cs) + "}`" for cs in cells)
    plain = expr.replace("(p : ℝ)", "p")
    out = f"""\
/-- The certificate for `2^{a} p^{b}` from `p ≥ {p0}` ({cert["nodes"]} search nodes). -/
theorem cert_{a}_{b} : certifyP {a} {b} {p0} {cert["w"]} {cert["D"]} {energy}
    {_lean_list(map(str, cert["order"]))}
    {_lean_bools(masks[0])}
    {_lean_list(_lean_bools(mk) for mk in masks[1:])} = true := by
  decide +kernel

/-- **`n = 2^{a} p^{b}`.** For every prime `p ≥ {p0}` and every set `S` of proper divisors of `n`,
the energy of `ICG(n, S)` is at most `{plain}`, with equality exactly for
{docsets}. -/
theorem energy_{a}_{b} {{p : ℕ}} (hp : p.Prime) (hp0 : {p0} ≤ p) {{S : Finset ℕ}}
    (hS : S ⊆ (2 ^ {a} * p ^ {b}).properDivisors) :
    {graph} ≤
        {expr} ∧
      ({graph} =
          {expr} ↔ {sets}) := by
  have h := energy_le_of_certifyP cert_{a}_{b} hp (by omega) hp0 hS
  have hE : ((UPoly.eval {energy} (p : ℤ) : ℤ) : ℝ) = {expr} := by
    simp only [UPoly.eval_cons, UPoly.eval_nil]; push_cast; ring
"""
    for j, (mk, cs) in enumerate(zip(masks, cells)):
        out += f"""\
  have h{j} : divsOfMask {a} {b} p {_lean_bools(mk)} = {{{_divisors(cs)}}} := by
    rw [show divsOfMask {a} {b} p {_lean_bools(mk)} =
      ([{_divisors(cs)}] : List ℕ).toFinset from rfl]
    simp
"""
    names = ", ".join(f"h{j}" for j in range(len(masks)))
    out += f"""\
  rw [hE] at h
  simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, {names}]
    using h

"""
    return out


def render_small_prime(cert):
    a, b, p, energy = cert["a"], cert["b"], cert["p"], cert["energy"]
    masks, cells = cert["masks"], cert["cells"]
    n = 2**a * p**b
    graph = f"ICGBridge.energy (ICGBridge.icgAdj {n} S) (ICGBridge.icgAdj_isHermitian _ _)"
    numbers = [sorted(2**c * p**e for c, e in cs) for cs in cells]
    sets = " ∨ ".join("S = {" + ", ".join(map(str, ns)) + "}" for ns in numbers)
    docsets = ", ".join("`{" + ", ".join(map(str, ns)) + "}`" for ns in numbers)
    out = f"""\
/-- The certificate for `2^{a} · {p}^{b} = {n}`, below the family's `p₀`. -/
theorem certAt_{a}_{b}_{p} : certifyAt {a} {b} {p} {energy}
    {_lean_bools(masks[0])}
    {_lean_list(_lean_bools(mk) for mk in masks[1:])} = true := by
  decide +kernel

/-- **`n = {n} = 2^{a} · {p}^{b}`.** For every set `S` of proper divisors of `{n}`, the energy of
`ICG({n}, S)` is at most `{energy}`, with equality exactly for {docsets}. -/
theorem energy_{a}_{b}_at_{p} {{S : Finset ℕ}} (hS : S ⊆ Nat.properDivisors {n}) :
    {graph} ≤ {energy} ∧
      ({graph} = {energy} ↔
        {sets}) := by
  have h := energy_le_of_certifyAt certAt_{a}_{b}_{p} (by norm_num) (by norm_num)
    (show S ⊆ (2 ^ {a} * {p} ^ {b}).properDivisors by simpa using hS)
"""
    for j, (mk, ns) in enumerate(zip(masks, numbers)):
        out += f"""\
  have h{j} : divsOfMask {a} {b} {p} {_lean_bools(mk)} = {{{", ".join(map(str, ns))}}} := by
    decide
"""
    names = ", ".join(f"h{j}" for j in range(len(masks)))
    out += f"""\
  push_cast at h
  simpa only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, {names}]
    using h

"""
    return out


def _even(records):
    return [r for r in records if r["result"]["kind"] == "one-symbolic" and r["order"][0][0] == 2]


def render(records):
    body = ""
    for r in _even(records):
        body += render_family(family_certificate(r))
        body += "".join(render_small_prime(c) for c in small_prime_certificates(r))
    return HEADER + body + "end Solved.ICG.Families\n"


def render_from(path):
    return render(json.loads(Path(path).read_text()))


GENERAL = {
    "formal/Formal/ICG/EvenCert.lean": ["Solved.ICG.certify_sound"],
    "formal/Formal/ICG/EvenPacked.lean": ["Solved.ICG.certifyP_sound"],
    "formal/Formal/ICG/EvenGraph.lean": ["Solved.ICG.energy_le_of_certifyP"],
    "formal/Formal/ICG/EvenAt.lean": [
        "Solved.ICG.certifyAt_sound",
        "Solved.ICG.energy_le_of_certifyAt",
    ],
    "formal/Formal/ICG/MultiBridge.lean": ["Solved.ICG.Multi.energy_icgAdj_multi"],
    "formal/Formal/ICG/MultiPacked.lean": ["Solved.ICG.Multi.certifyM_sound"],
    "formal/Formal/ICG/MultiGraph.lean": ["Solved.ICG.Multi.energy_le_of_certifyM"],
}
FAMILIES = "formal/Formal/ICG/EvenFamilies.lean"

AXIOMS = "[propext, Classical.choice, Quot.sound]"


def family_theorems(records):
    names = []
    for r in _even(records):
        a, b = r["order"][0][1], r["order"][1][1]
        names.append(f"Solved.ICG.Families.energy_{a}_{b}")
        names += [
            f"Solved.ICG.Families.energy_{a}_{b}_at_{p}"
            for p in sorted(map(int, r["result"]["small_primes"]))
        ]
    return names


def registry(records):
    """The theorem registry of the Mathlib project: exactly the theorems the audit covers."""
    modules = [{"file": f, "theorems": names} for f, names in GENERAL.items()]
    modules.append({"file": FAMILIES, "theorems": family_theorems(records)})
    return {
        "toolchain": "leanprover/lean4:v4.34.1",
        "project": "formal",
        "audit": "formal/FormalTests/Axioms.lean",
        "scope": (
            "Kernel-checked energy certificates for integral circulant graphs, built with Mathlib "
            "and H. Dong's ai4math-results bridge. The audit file fails the build unless each "
            "registered theorem depends only on propext, Classical.choice and Quot.sound."
        ),
        "modules": modules,
    }


def render_registry(records):
    return json.dumps(registry(records), indent=2, ensure_ascii=False) + "\n"


def render_axioms(records):
    """A test file that fails to build unless every theorem rests on the standard axioms only."""
    names = [n for module in registry(records)["modules"] for n in module["theorems"]]
    out = """\
import Formal

/-!
# Axiom audit for the energy certificates

Generated by `python -m scripts.lean_icg_families`; do not edit by hand. `#guard_msgs` fails the
build unless each theorem depends on exactly the standard axioms `propext`, `Classical.choice`
and `Quot.sound`: no `sorryAx`, and no `Lean.ofReduceBool` from `native_decide`.
-/
"""
    for name in names:
        out += f"""
/-- info: '{name}' depends on axioms: {AXIOMS} -/
#guard_msgs in
#print axioms {name}
"""
    return out


def axioms_from(path):
    return render_axioms(json.loads(Path(path).read_text()))


def registry_from(path):
    return render_registry(json.loads(Path(path).read_text()))


# --- the results table of results/icg-energy-even-orders/PROOF.md ----------------------------

TABLE_BEGIN = "<!-- BEGIN GENERATED TABLE -->"
TABLE_END = "<!-- END GENERATED TABLE -->"


def _divisor_text(c, e):
    """2^c p^e in LaTeX, e.g. 4p^{2}."""
    two = "" if c == 0 else str(2**c)
    prime = "" if e == 0 else "p" if e == 1 else f"p^{{{e}}}"
    return two + prime or "1"


def _math_set(items):
    return "$\\{" + ",".join(items) + "\\}$"


def _poly_text(coeffs):
    """A polynomial in p in LaTeX, highest degree first."""
    terms = []
    for i, c in reversed(list(enumerate(coeffs))):
        if c == 0:
            continue
        mono = "" if i == 0 else "p" if i == 1 else f"p^{{{i}}}"
        body = str(abs(c)) if i == 0 else mono if abs(c) == 1 else f"{abs(c)}{mono}"
        terms.append(("-" if c < 0 else "+", body))
    out = ("-" if terms[0][0] == "-" else "") + terms[0][1]
    for sign, body in terms[1:]:
        out += f"{sign}{body}"
    return out


def render_table(records):
    rows = [
        TABLE_BEGIN,
        "",
        "| Order | Primes | Maximal energy | Maximising divisor sets | Lean theorem |",
        "|---|---|---|---|---|",
    ]
    for r in _even(records):
        cert = family_certificate(r)
        a, b = cert["a"], cert["b"]
        order = ("2" if a == 1 else f"2^{{{a}}}") + ("p" if b == 1 else f"p^{{{b}}}")
        sets = "; ".join(
            _math_set(_divisor_text(c, e) for c, e in sorted(cs, key=lambda t: (t[1], t[0])))
            for cs in cert["cells"]
        )
        rows.append(
            f"| ${order}$ | $p\\ge{cert['p0']}$ | ${_poly_text(cert['energy'])}$ | {sets} "
            f"| `energy_{a}_{b}` |"
        )
        for small in small_prime_certificates(r):
            p = small["p"]
            n = 2 ** small["a"] * p ** small["b"]
            sets = "; ".join(
                _math_set(map(str, sorted(2**c * p**e for c, e in cs))) for cs in small["cells"]
            )
            rows.append(
                f"| ${n}$ | $p={p}$ | ${small['energy']}$ | {sets} | `energy_{a}_{b}_at_{p}` |"
            )
    rows.extend(["", TABLE_END])
    return "\n".join(rows)


def update_table(text, records):
    if text.count(TABLE_BEGIN) != 1 or text.count(TABLE_END) != 1:
        raise ValueError("the manuscript needs exactly one generated table")
    start, end = text.index(TABLE_BEGIN), text.index(TABLE_END) + len(TABLE_END)
    return text[:start] + render_table(records) + text[end:]


def table_from(path, manuscript):
    return update_table(Path(manuscript).read_text(), json.loads(Path(path).read_text()))


# --- multi-prime orders on a region (Formal/ICG/MultiPacked.lean) ----------------------------


def badd(P, Q):
    """BPoly.add: rowwise UPoly.add, the shorter list padded with empty rows."""
    n = max(len(P), len(Q))
    return [padd(P[i] if i < len(P) else [], Q[i] if i < len(Q) else []) for i in range(n)]


def bscale(c, P):
    return [pscale(c, row) for row in P]


def bmul_lin(c0, c1, c2, P):
    """BPoly.mulLin: (c0 + c1 x + c2 y) * P."""
    return badd(bscale(c0, P), badd(bscale(c1, [[]] + P), bscale(c2, [[0] + row for row in P])))


def bcompose(f, c0, c1, c2):
    """BPoly.compose: f(c0 + c1 x + c2 y)."""
    if not f:
        return []
    return badd([[f[0]]], bmul_lin(c0, c1, c2, bcompose(f[1:], c0, c1, c2)))


def bmul(P, Q):
    """BPoly.mul: mul (A :: P) Q = add (Q.map (UPoly.mul A)) (mulX (mul P Q))."""
    if not P:
        return []
    return badd([pmul(P[0], row) for row in Q], [[]] + bmul(P[1:], Q))


def bsubst(E, s1, s2):
    """BPoly.subst: E(s1, s2) for affine forms s = (c0, c1, c2)."""
    if not E:
        return []
    return badd(bcompose(E[0], *s2), bmul_lin(*s1, bsubst(E[1:], s1, s2)))


def bcoeff(P, i, j):
    return P[i][j] if i < len(P) and j < len(P[i]) else 0


def bflat(Dx, Dy, P):
    return [bcoeff(P, d // Dy, d % Dy) for d in range(Dx * Dy)]


def beval(P, x, y):
    return sum(peval(row, y) * x**i for i, row in enumerate(P))


def mixed_dec(a, e):
    """Box.dec: little-endian mixed-radix digits with radices a_i + 1."""
    out = []
    for ai in a:
        out.append(e % (ai + 1))
        e //= ai + 1
    return out


def mixed_enc(a, x):
    code, stride = 0, 1
    for ai, xi in zip(a, x):
        code += xi * stride
        stride *= ai + 1
    return code


class MultiShape:
    """Shape: exponents, slots (0 fixed, 1 = p, 2 = q), fixed primes, affine forms."""

    def __init__(self, factors, s1, s2):
        self.a = [e for _, e in factors]
        self.slot = [1 if r == "p" else 2 if r == "q" else 0 for r, _ in factors]
        self.fixed = [r if isinstance(r, int) else 0 for r, _ in factors]
        self.s1, self.s2 = s1, s2
        self.size = 1
        for ai in self.a:
            self.size *= ai + 1

    def factor(self, u, c, i):
        t = tent_p(self.a[i], u[i], c[i])
        if self.slot[i] == 1:
            return bcompose(t, *self.s1)
        if self.slot[i] == 2:
            return bcompose(t, *self.s2)
        return [[peval(t, self.fixed[i])]]

    def cell(self, e, kc):
        u, c = mixed_dec(self.a, e), mixed_dec(self.a, kc)
        out = [[1]]
        for i in reversed(range(len(self.a))):
            out = bmul(self.factor(u, c, i), out)
        return out


def regions(p0):
    """The two regions of the Python certificates: (name, sigma_p, sigma_q)."""
    return [("lt", (p0, 1, 0), (p0 + 2, 1, 1)), ("gt", (p0 + 2, 1, 1), (p0, 0, 1))]


def search_tables(tables, target, order, m, D):
    """Nodes and unpruned leaves of `bnbP` on flat tables (cell -> m entries of D coefficients)."""
    suffix_s = [[[0] * D for _ in range(m)]]
    suffix_lo = [[[0] * D for _ in range(m)]]
    for kc in reversed(order):
        prev_s, prev_lo = suffix_s[0], suffix_lo[0]
        suffix_s.insert(0, [[s + t for s, t in zip(prev_s[e], tables[kc][e])] for e in range(m)])
        suffix_lo.insert(
            0, [[lo + min(t, 0) for lo, t in zip(prev_lo[e], tables[kc][e])] for e in range(m)]
        )
    nodes, leaves = 0, []

    def passes(depth, acc):
        z = list(target)
        for e in range(m):
            for d in range(D):
                a_ed = acc[e][d]
                z[d] += a_ed + suffix_lo[depth][e][d] - max(2 * a_ed + suffix_s[depth][e][d], 0)
        return z[0] > 0 and all(v >= 0 for v in z)

    def go(depth, path, acc):
        nonlocal nodes
        nodes += 1
        if passes(depth, acc):
            return
        if depth == len(order):
            leaves.append(path)
            return
        kc = order[depth]
        go(depth + 1, path, acc)
        row = tables[kc]
        go(depth + 1, path | 1 << kc, [[x + y for x, y in zip(acc[e], row[e])] for e in range(m)])

    go(0, 0, [[0] * D for _ in range(m)])
    return nodes, leaves


def _multi_orders(shape):
    cells = list(range(shape.size - 1))
    out = {"natural": cells, "reverse": cells[::-1]}
    for lead in range(len(shape.a)):
        name = f"coordinate {lead} first"
        out[name] = sorted(
            cells,
            key=lambda kc: (-mixed_dec(shape.a, kc)[lead], [-v for v in mixed_dec(shape.a, kc)]),
        )
    return out


def multi_certificate(record, region_name):
    """Lean data for certifyM: one two-symbolic family on one region ("lt": p < q, "gt": p > q)."""
    result = record["result"]
    p0 = result["smallest_symbolic_prime"]
    name, s1, s2 = next(r for r in regions(p0) if r[0] == region_name)
    data = result["p<q" if name == "lt" else "p>q"]
    if data["certificate"] != "exact":
        raise ValueError("only exact region certificates are supported here")
    shape = MultiShape(record["order"], s1, s2)
    N = shape.size
    cells = [[shape.cell(e, kc) for e in range(N)] for kc in range(N - 1)]
    deg = {}
    for i, j, c in data["energy"]:
        deg[(i, j)] = deg.get((i, j), 0) + c
    E = [
        [deg.get((i, j), 0) for j in range(1 + max(j for _, j in deg))]
        for i in range(1 + max(i for i, _ in deg))
    ]
    tgt = bsubst(E, s1, s2)
    Dx = max([len(P) for row in cells for P in row] + [len(tgt)])
    Dy = max([len(r) for row in cells for P in row for r in P] + [len(r) for r in tgt])
    D = Dx * Dy
    tables = [[bflat(Dx, Dy, P) for P in row] for row in cells]
    target = bflat(Dx, Dy, tgt)
    masks = []
    for divisor_set in data["maximisers"]:
        mask = [False] * (N - 1)
        for c in divisor_set:
            mask[mixed_enc(shape.a, c)] = True
        masks.append(mask)
    expected = sorted(sum(1 << k for k, bit in enumerate(mk) if bit) for mk in masks)
    best = None
    for oname, order in _multi_orders(shape).items():
        nodes, leaves = search_tables(tables, target, order, N, D)
        if sorted(leaves) != expected:
            raise ValueError(f"unpruned leaves differ from the maximisers ({oname})")
        if best is None or nodes < best[0]:
            best = (nodes, oname, order)
    nodes, oname, order = best
    total = sum(abs(c) for kc in order for f in tables[kc] for c in f)
    tail = sum(abs(c) for c in target)
    w = (4 * N * total + tail).bit_length() + 1
    return {
        "order": record["order"],
        "region": name,
        "p0": p0,
        "shape": shape,
        "w": w,
        "Dx": Dx,
        "Dy": Dy,
        "E": E,
        "ks": order,
        "order_name": oname,
        "nodes": nodes,
        "masks": masks,
        "cells": data["maximisers"],
    }


def multi_label(order):
    """A Lean-identifier label for an order, e.g. 2_p2_q for 2 p^2 q, 6_p_q for 6pq."""
    fixed = 1
    parts = []
    for r, e in order:
        if isinstance(r, int):
            fixed *= r**e
        else:
            parts.append(r if e == 1 else f"{r}{e}")
    return "_".join([str(fixed)] + parts)


def _lean_vec(xs):
    return "![" + ", ".join(map(str, xs)) + "]"


def render_multi_cert(cert):
    s = cert["shape"]
    label = multi_label(cert["order"]) + "_" + cert["region"]
    region = (
        f"p ≥ {cert['p0']}, q ≥ p + 2" if cert["region"] == "lt" else f"q ≥ {cert['p0']}, p ≥ q + 2"
    )
    E = "[" + ", ".join(_lean_list(map(str, row)) for row in cert["E"]) + "]"
    return f"""\
/-- The order `{multi_label(cert["order"]).replace("_", " ")}` on the region `{region}`. -/
def shape_{label} : Shape {len(s.a)} :=
  ⟨{_lean_vec(s.a)}, {_lean_vec(s.slot)}, {_lean_vec(s.fixed)}, ⟨{s.s1[0]}, {s.s1[1]}, {s.s1[2]}⟩,
    ⟨{s.s2[0]}, {s.s2[1]}, {s.s2[2]}⟩⟩

/-- The certificate for `{label}` ({cert["nodes"]} search nodes). -/
theorem cert_{label} : certifyM shape_{label} {cert["w"]} {cert["Dx"]} {cert["Dy"]} {E}
    {_lean_list(map(str, cert["ks"]))}
    {_lean_bools(cert["masks"][0])}
    {_lean_list(_lean_bools(mk) for mk in cert["masks"][1:])} = true := by
  decide +kernel

"""


MULTI_HEADER = """\
import Formal.ICG.MultiGraph

/-!
# Maximal energy of multi-prime `ICG(n, S)`: kernel-checked region certificates

Generated by `python -m scripts.lean_icg_families` from `checks/expected/icg-families.json`;
do not edit by hand. Each certificate covers one order with two symbolic primes `p, q` on one
region, `p ≥ p₀, q ≥ p + 2` (`lt`) or `q ≥ p₀, p ≥ q + 2` (`gt`); `energy_le_of_certifyM` turns
it into a statement about graph energy at every pair of distinct primes in the region.
-/

namespace Solved.ICG.Multi.Families

open Solved.Cert Solved.ICG.Multi

"""


def render_multi(records):
    body = ""
    for r in records:
        if r["result"]["kind"] != "two-symbolic":
            continue
        for region in ("lt", "gt"):
            key = "p<q" if region == "lt" else "p>q"
            if r["result"][key]["certificate"] != "exact":
                continue
            body += render_multi_cert(multi_certificate(r, region))
    return MULTI_HEADER + body + "end Solved.ICG.Multi.Families\n"


def multi_from(path):
    return render_multi(json.loads(Path(path).read_text()))
