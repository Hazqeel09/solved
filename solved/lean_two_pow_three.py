"""Generate formal/Formal/ICG/TwoPowThree.lean: the maximal energy of ICG(2^a * 3, S).

The Lean module proves `energy_max_three` and `energy_max_odd`. Its hand-written parts live in
`solved/templates/two_pow_three/`; this module adds the numeric step lemmas. Each such lemma is a
piecewise-linear inequality on the unit square. The generator splits the square by the signs of the
absolute values and, where one right-hand piece does not cover a whole cell, by further linear forms
(exact rational polygon clipping), and records the covering piece for every cell. Lean re-checks
every cell with `linarith`; nothing here is trusted.

Affine forms are triples (c, a, b) meaning c + a*s + b*t with Fraction coefficients.
"""

from fractions import Fraction as F
from pathlib import Path

TEMPLATES = Path(__file__).parent / "templates" / "two_pow_three"
P = 3
BITS = [(0, 0), (1, 0), (0, 1), (1, 1)]
BOXH = "(hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)"
LO, HI = F(-1, 8), F(1, 16)

# --- affine geometry on the unit square -------------------------------------------------------

SQUARE = [(F(0), F(0)), (F(1), F(0)), (F(1), F(1)), (F(0), F(1))]
BOX = [(F(0), F(1), F(0)), (F(1), F(-1), F(0)), (F(0), F(0), F(1)), (F(1), F(0), F(-1))]


def ev(q, p):
    return q[0] + q[1] * p[0] + q[2] * p[1]


def add(q, r):
    return (q[0] + r[0], q[1] + r[1], q[2] + r[2])


def sub(q, r):
    return (q[0] - r[0], q[1] - r[1], q[2] - r[2])


def scale(k, q):
    return (k * q[0], k * q[1], k * q[2])


def clip(poly, h):
    """The part of a convex polygon where h >= 0 (exact Sutherland-Hodgman step)."""
    out = []
    for i, p in enumerate(poly):
        q = poly[(i + 1) % len(poly)]
        hp, hq = ev(h, p), ev(h, q)
        if hp >= 0:
            out.append(p)
        if (hp > 0 > hq) or (hp < 0 < hq):
            lam = hp / (hp - hq)
            out.append((p[0] + lam * (q[0] - p[0]), p[1] + lam * (q[1] - p[1])))
    res = []
    for v in out:
        if not res or res[-1] != v:
            res.append(v)
    if len(res) > 1 and res[0] == res[-1]:
        res.pop()
    return res


def region(constraints):
    poly = SQUARE[:]
    for h in constraints:
        poly = clip(poly, h)
        if not poly:
            return []
    return poly


def fmt(q):
    def num(x):
        if x.denominator == 1:
            return f"({x.numerator} : ℝ)"
        return f"({x.numerator} / {x.denominator} : ℝ)"

    return f"{num(q[0])} + {num(q[1])} * s + {num(q[2])} * t"


# --- the pieces of the value function (must match the definitions in head.lean) ---------------

_L = [
    (F(0), F(-8, 3), F(2, 3)),
    (F(-2), F(8, 3), F(-2, 3)),
    (F(0), F(-4, 3), F(-8, 3)),
    (F(-4), F(4, 3), F(8, 3)),
]
_PSI = [
    add((F(8, 9), F(0), F(0)), scale(2, _L[0])),
    add((F(8, 9), F(0), F(0)), scale(2, _L[1])),
    (F(-28, 9), F(16, 3), F(-4, 3)),
    (F(8, 9), F(-16, 3), F(4, 3)),
]


def tp(i, rho):
    """Tp i rho = L_i + rho psi_i."""
    return add(_L[i], scale(rho, _PSI[i]))


P0 = [(F(0), F(0), F(6)), (F(0), F(8), F(-2))]
P1 = [(F(4), F(4), F(2)), (F(6), F(-4), F(4)), (F(6), F(4), F(-4)), (F(8), F(0), F(0))]
P2 = [add((F(106, 9), F(0), F(0)), tp(i, F(1, 4))) for i in range(4)] + [
    (F(106, 9) + F(2, 9), F(-2), F(-1)),
    (F(106, 9) - F(25, 9), F(2), F(1)),
]
W3 = [add((F(10) + F(46, 9), F(0), F(0)), tp(i, F(-1, 8))) for i in range(4)]


def compose(q, z, w):
    """q((s + z)/2, (t + w)/2)."""
    return (q[0] + q[1] * F(z, 2) + q[2] * F(w, 2), q[1] / 2, q[2] / 2)


def abs_args(z, w):
    """The arguments of the two absolute values of 2 F_3((z - s)/2, (w - t)/2), and their Lean text."""
    al = (F(z, 2), F(-1, 2), F(0))
    be = (F(w, 2), F(0), F(-1, 2))
    return (
        sub(be, al),
        add(scale(P - 1, al), be),
        f"({w} - t) / 2 - ({z} - s) / 2",
        f"(3 - 1) * (({z} - s) / 2) + ({w} - t) / 2",
    )


def two_f(z, w, e1, e2):
    a1, a2, _, _ = abs_args(z, w)
    return scale(2, add(scale((P - 1) * e1, a1), scale(e2, a2)))


# --- certificates: cell trees ------------------------------------------------------------------


def search(cons, need, depth=0):
    """A cell tree covering region(cons): ('empty',) | ('leaf', j) | ('split', e, pos, neg).

    `need[j]` lists the affine forms that must be >= 0 on a cell for choice j; validity on a convex
    cell is checked exactly at its vertices. A split on a form e that the best candidate violates
    keeps that candidate where e >= 0 and drops it where e <= 0, so the recursion terminates.
    """
    poly = region(cons)
    if not poly:
        return ("empty",)
    best, best_score, best_fail = None, -1, None
    for j, forms in need.items():
        fails = [e for e in forms for v in poly if ev(e, v) < 0]
        if not fails:
            return ("leaf", j)
        score = sum(1 for e in forms for v in poly if ev(e, v) >= 0)
        if score > best_score:
            best, best_score, best_fail = j, score, fails[0]
    rest = {j: f for j, f in need.items() if j != best}
    if not rest or depth > 12:
        raise RuntimeError("no certificate for this cell")
    e = best_fail
    return (
        "split",
        e,
        search(cons + [e], need, depth + 1),
        search(cons + [scale(-1, e)], rest, depth + 1),
    )


def verify(tree, cons, need):
    """Independent re-check of a cell tree: every leaf's forms are >= 0 at every cell vertex."""
    poly = region(cons)
    if tree[0] == "empty":
        return not poly
    if tree[0] == "leaf":
        return all(ev(e, v) >= 0 for e in need[tree[1]] for v in poly)
    _, e, pos, neg = tree
    return verify(pos, cons + [e], need) and verify(neg, cons + [scale(-1, e)], need)


def leaves(tree):
    if tree[0] == "leaf":
        return 1
    if tree[0] == "empty":
        return 0
    return leaves(tree[2]) + leaves(tree[3])


def emit_cell(tree, leaf_tac, ind, depth=0):
    if tree[0] == "empty":
        return f"{ind}linarith\n"
    if tree[0] == "leaf":
        return leaf_tac(tree[1], ind)
    _, e, pos, neg = tree
    h = f"hc{depth}"
    out = f"{ind}rcases le_total 0 ({fmt(e)}) with {h} | {h}\n"
    out += f"{ind}· " + emit_cell(pos, leaf_tac, ind + "  ", depth + 1).lstrip()
    out += f"{ind}· " + emit_cell(neg, leaf_tac, ind + "  ", depth + 1).lstrip()
    return out


def abs_split(z, w, cell):
    """Split on the signs of the two absolute values, then a cell proof per sign case."""
    _, _, s1, s2 = abs_args(z, w)
    out = f"  rcases le_total 0 ({s1}) with h1 | h1\n"
    for e1, lem1 in ((1, "abs_of_nonneg"), (-1, "abs_of_nonpos")):
        out += f"  · rw [{lem1} h1]\n    rcases le_total 0 ({s2}) with h2 | h2\n"
        for e2, lem2 in ((1, "abs_of_nonneg"), (-1, "abs_of_nonpos")):
            out += f"    · rw [{lem2} h2]\n" + cell(e1, e2, "      ")
    return out


def sign_cells(z, w):
    a1, a2, _, _ = abs_args(z, w)
    return [(e1, e2, BOX + [scale(e1, a1), scale(e2, a2)]) for e1 in (1, -1) for e2 in (1, -1)]


# --- max trees ---------------------------------------------------------------------------------

T4 = ((0, 1), (2, 3))
T6 = (((0, 1), (2, 3)), (4, 5))


def paths(tree, prefix=()):
    if isinstance(tree, int):
        return {tree: prefix}
    return {**paths(tree[0], prefix + ("left",)), **paths(tree[1], prefix + ("right",))}


def chain(path):
    """A proof that a leaf is at most the root of a max tree along `path`."""
    acc = None
    for d in reversed(path):
        step = f"(le_max_{d} _ _)"
        acc = step if acc is None else f"({acc}.trans {step})"
    return acc or "le_rfl"


# --- lemma families ----------------------------------------------------------------------------

UP = {  # name: (next pieces, Lean name of next piece, rhs pieces, rhs tree, rhs text, unfold, simp)
    "up01": (P0, "P0", P1, T4, "V1 s t", "Fp V1", "P0, P1"),
    "up12": (P1, "P1", P2, T6, "Q2 s t", "Fp Q2", "P1, P2, Tp"),
    "up23": (P2, "P2", W3, T4, "10 + 46 / 9 + U3 (-1 / 8) s t", "Fp U3", "P2, Tp"),
}

# Covering right-hand pieces for the steps n >= 3, per bits (z, w) and next piece i.
COVER = {
    (0, 0): {0: (0, 1, 3), 1: (0, 1), 2: (0, 1), 3: (1,)},
    (1, 0): {0: (0,), 1: (0, 3), 2: (0,), 3: (0, 1)},
    (0, 1): {0: (1, 2), 1: (1,), 2: (0, 1), 3: (1,)},
    (1, 1): {0: (0, 1), 1: (0, 1, 2), 2: (0,), 3: (0, 1)},
}

# Attainment: for each piece of the current state, bits (z, w) and the next piece that cover it.
ATT01 = {0: ((1, 0), 1), 1: ((1, 1), 0), 2: ((1, 1), 1), 3: ((1, 0), 1)}
ATT12 = {
    0: ((1, 0), 3),
    1: ((0, 1), 3),
    2: ((0, 1), 3),
    3: ((0, 0), 3),
    4: ((1, 0), 2),
    5: ((0, 1), 1),
}
ATT23 = {0: ((1, 0), 1), 1: ((0, 1), 0), 2: ((0, 1), 0), 3: ((1, 0), 1)}
ATTN = {0: ((1, 0), 1), 1: ((0, 1), 0), 2: ((0, 1), 0), 3: ((1, 0), 1)}


def slack(z, w, i, j, rho, e1, e2):
    return sub(
        add((F(10, 3), F(0), F(0)), tp(j, F(-1, 2) * rho)),
        add(two_f(z, w, e1, e2), compose(tp(i, rho), z, w)),
    )


def up_lemma(fam, z, w, i):
    nxt, nname, rhs, tree, rhs_text, unfold, simp = UP[fam]
    pth = paths(tree)
    wrap = fam == "up23"

    def cell(e1, e2, ind):
        cons = next(c for a, b, c in sign_cells(z, w) if (a, b) == (e1, e2))
        lhs = add(two_f(z, w, e1, e2), compose(nxt[i], z, w))
        need = {j: [sub(rhs[j], lhs)] for j in pth}
        tr = search(cons, need)
        assert verify(tr, cons, need)

        def leaf(j, ind2):
            c = chain(pth[j])
            if wrap:
                c = f"(add_le_add le_rfl {c})"
            return f"{ind2}refine le_trans ?_ {c}\n{ind2}linarith\n"

        return emit_cell(tr, leaf, ind)

    return (
        f"\ntheorem {fam}_{z}{w}_{i} {{s t : ℝ}} {BOXH} :\n"
        f"    2 * Fp 3 (({z} - s) / 2) (({w} - t) / 2) + {nname} {i} ((s + {z}) / 2) ((t + {w}) / 2) ≤\n"
        f"      {rhs_text} := by\n  unfold {unfold}\n  simp only [{simp}]\n" + abs_split(z, w, cell)
    )


def cov_lemma(z, w, i, js):
    terms = [
        f"min (slk {z} {w} {i} {j} (-1 / 8) s t) (slk {z} {w} {i} {j} (1 / 16) s t)" for j in js
    ]
    stmt = terms[0]
    for tm in terms[1:]:
        stmt = f"max ({stmt})\n      ({tm})"
    tree = {1: 0, 2: (0, 1), 3: ((0, 1), 2)}[len(js)]
    pth = paths(tree)

    def cell(e1, e2, ind):
        cons = next(c for a, b, c in sign_cells(z, w) if (a, b) == (e1, e2))
        need = {
            k: [slack(z, w, i, j, LO, e1, e2), slack(z, w, i, j, HI, e1, e2)]
            for k, j in enumerate(js)
        }
        tr = search(cons, need)
        assert verify(tr, cons, need)

        def leaf(k, ind2):
            return f"{ind2}refine le_trans (le_min ?_ ?_) {chain(pth[k])}\n{ind2}· linarith\n{ind2}· linarith\n"

        return emit_cell(tr, leaf, ind)

    return (
        f"\ntheorem cov_{z}{w}_{i} {{s t : ℝ}} {BOXH} :\n    0 ≤ {stmt} := by\n"
        f"  unfold slk Fp\n  simp only [Tp]\n" + abs_split(z, w, cell)
    )


def _plain(name, stmt, unfold, simp):
    """A lemma whose only case split is on the two absolute values (used for attainment)."""
    return (
        f"\ntheorem {name} {{s t : ℝ}} {BOXH} :\n    {stmt} := by\n  unfold {unfold}\n"
        f"  simp only [{simp}]\n  simp only [abs_eq_max_neg, max_def]\n  split_ifs <;> linarith\n"
    )


def att_lemmas():
    nxt = lambda z, w: f"((s + {z}) / 2) ((t + {w}) / 2)"  # noqa: E731
    f2 = lambda z, w: f"2 * Fp 3 (({z} - s) / 2) (({w} - t) / 2)"  # noqa: E731
    out = []
    for j, ((z, w), i) in ATT01.items():
        out.append(
            _plain(f"at01_{j}", f"P1 {j} s t ≤ {f2(z, w)} + P0 {i} {nxt(z, w)}", "Fp", "P0, P1")
        )
    for j, ((z, w), i) in ATT12.items():
        simp = "P1, P2, Tp" if j < 4 else "P1, P2"
        out.append(_plain(f"at12_{j}", f"P2 {j} s t ≤ {f2(z, w)} + P1 {i} {nxt(z, w)}", "Fp", simp))
    for j, ((z, w), i) in ATT23.items():
        out.append(
            _plain(
                f"at23_{j}",
                f"10 + 46 / 9 + Tp {j} (-1 / 8) s t ≤ {f2(z, w)} + P2 {i} {nxt(z, w)}",
                "Fp",
                "P2, Tp",
            )
        )
    for j, ((z, w), k) in ATTN.items():
        for nm, rho in (("lo", "(-1 / 8)"), ("hi", "(1 / 16)")):
            out.append(
                _plain(f"atr_{j}_{nm}", f"0 ≤ slkA {z} {w} {j} {k} {rho} s t", "slkA Fp", "Tp")
            )
    return out


def use_j(h, j, ind):
    return (
        f"{ind}obtain ⟨hlo, hhi⟩ := le_min_iff.1 {h}\n{ind}have e := slk_mid hρ0 hρ1 hlo hhi\n"
        f"{ind}unfold slk at e\n{ind}have := Tp_le_U3 (j := {j}) (by norm_num) (-1 / 2 * ρ) s t\n"
        f"{ind}linarith\n"
    )


def step_lemmas():
    out = []
    for (z, w), d in COVER.items():
        for i, js in d.items():
            body = f"  have hc := cov_{z}{w}_{i} hs0 hs1 ht0 ht1\n"
            if len(js) == 1:
                body += use_j("hc", js[0], "  ")
            elif len(js) == 2:
                body += "  rcases le_max_iff.1 hc with h | h\n"
                body += "  · " + use_j("h", js[0], "    ").lstrip()
                body += "  · " + use_j("h", js[1], "    ").lstrip()
            else:
                body += (
                    "  rcases le_max_iff.1 hc with h | h\n  · rcases le_max_iff.1 h with h | h\n"
                )
                body += "    · " + use_j("h", js[0], "      ").lstrip()
                body += "    · " + use_j("h", js[1], "      ").lstrip()
                body += "  · " + use_j("h", js[2], "    ").lstrip()
            out.append(
                f"\ntheorem stepU_{z}{w}_{i} {{ρ s t : ℝ}} {BOXH}\n    (hρ0 : -1 / 8 ≤ ρ) (hρ1 : ρ ≤ 1 / 16) :\n"
                f"    2 * Fp 3 (({z} - s) / 2) (({w} - t) / 2) + Tp {i} ρ ((s + {z}) / 2) ((t + {w}) / 2) ≤\n"
                f"      10 / 3 + U3 (-1 / 2 * ρ) s t := by\n{body}"
            )
    return out


def certificate_summary():
    """Number of leaves per numeric lemma (for tests and the manuscript)."""
    total = 0
    for fam in UP:
        for z, w in BITS:
            for i in range(len(UP[fam][0])):
                for e1, e2, cons in sign_cells(z, w):
                    lhs = add(two_f(z, w, e1, e2), compose(UP[fam][0][i], z, w))
                    need = {j: [sub(UP[fam][2][j], lhs)] for j in paths(UP[fam][3])}
                    total += leaves(search(cons, need))
    return total


def render():
    numeric = []
    for fam, spec in UP.items():
        for z, w in BITS:
            for i in range(len(spec[0])):
                numeric.append(up_lemma(fam, z, w, i))
    for (z, w), d in COVER.items():
        for i, js in d.items():
            numeric.append(cov_lemma(z, w, i, js))
    numeric += att_lemmas()
    parts = [
        (TEMPLATES / "head.lean").read_text(),
        "".join(numeric),
        (TEMPLATES / "general.lean").read_text(),
        "".join(step_lemmas()),
    ]
    parts += [(TEMPLATES / f"{n}.lean").read_text() for n in ("steps", "attain", "chain", "graph")]
    return "".join(parts) + "\nend Solved.ICG.TwoPow\n"


def render_from(_source=None):
    return render()
