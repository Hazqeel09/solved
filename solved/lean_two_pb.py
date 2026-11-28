"""Generate the step certificates of the 2p^b energy chain as Lean modules (formal/Formal/ICG/TwoPb/).

Input: checks/expected/two-pb-certificates.json (untrusted search output). Every inequality is
re-checked by Lean; nothing here is trusted.

Setting. For an odd prime p let y = p - 3 >= 0 and x = 1/p = 1/(y + 3). The chain state is u = (s, t) in
the unit square; one step to the corner c = (c0, c1) moves u to u' = x u + (1 - x) c and gains
2 (1 - x) max(|c0 - s|, |c1 - t|). The value function with n >= 1 steps left is bounded by
W_n(u) = n g + max_i Q_{k,i}(mu; u), k = n mod 4, mu = x^n, g = 2(1 - x)/(1 + x^2).

Scaling. With tau = mu (y + 3)^m_k in [0, 1] (m_k the least n >= n0 with n = k mod 4) every piece
coefficient is a rational function of y whose denominator divides one polynomial K(y). The Lean modules
use the polynomial pieces Qh = K Q(y, tau, s, t), Kg = K g and Kgain = K 2 (1 - x).

Candidate lemma (residue k, piece i, corner c, coordinate j). With s', t', tau' given by
(y+3) s' = s + (y+2) c0, (y+3) t' = t + (y+2) c1 and (y+3)^e tau' = tau (e = 4 for k = 0, else 0):
  Kgain d_j + Qh_{k,i}(tau; s', t') - Kg <= Mx_{k+1}(tau'; s, t),
where d_j = 1 - u_j if c_j = 1 else u_j. Proof: weights N_l (y, tau) >= 0 with sum M > 0 such that
E (sum_l N_l Qh_{k+1,l} - M cand) = A + B s + C t (one linear_combination), and the four corner
values A, A+B, A+C, A+B+C are nonnegative on tau in [0, 1] in Bernstein form with coefficients that are
polynomials in y with nonnegative coefficients (positivity).
"""

import json
from functools import reduce
from math import comb
from pathlib import Path

from sympy import (
    Poly,
    Rational,
    cancel,
    expand,
    factor_list,
    fraction,
    lcm,
    symbols,
    sympify,
    together,
)

ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "checks" / "expected" / "two-pb-certificates.json"
OUT = ROOT / "formal" / "Formal" / "ICG" / "TwoPb"
NS = "Solved.ICG.TwoPb"

x, y, mu, tau, s, t, s1, t1, tau1 = symbols("x y mu tau s t s1 t1 tau1")
X = 1 / (y + 3)
CORNERS = [(0, 0), (1, 0), (0, 1), (1, 1)]
FIELDS = ("const", "const_xn", "s", "s_xn", "t", "t_xn")


# --- data -------------------------------------------------------------------------------------

def load(source=SOURCE):
    return json.loads(Path(source).read_text())


def m_of(k, n0):
    n = n0
    while n % 4 != k:
        n += 1
    return n


def rat_y(e):
    return cancel(together(sympify(e).subs(x, X)))


class Model:
    """Pieces in (y, tau), the common denominator K and the scaled polynomial pieces."""

    def __init__(self, data):
        self.data = data
        self.n0 = data["n0"]
        self.m = {k: m_of(k, self.n0) for k in range(4)}
        self.raw = {}
        dens = []
        for k in range(4):
            rows = []
            for P in data["pieces"][str(k)]:
                c = [rat_y(P[f]) for f in FIELDS]
                sc = X ** self.m[k]  # mu = tau x^m
                row = (c[0], cancel(c[1] * sc), c[2], cancel(c[3] * sc), c[4], cancel(c[5] * sc))
                rows.append(row)
                dens += [fraction(e)[1] for e in row]
            self.raw[k] = rows
        self.g = rat_y(2 * (1 - x) / (1 + x**2))
        self.gain = rat_y(2 * (1 - x))
        dens += [fraction(self.g)[1], fraction(self.gain)[1]]
        self.K = expand(reduce(lambda a, b: lcm(a, b), [Poly(d, y).as_expr() for d in dens]))
        for fac, _ in factor_list(self.K)[1]:
            if Poly(fac, y).degree() > 0 and fac not in (y + 3, y**2 + 6 * y + 10):
                raise ValueError(f"unexpected denominator factor {fac}")
        self.Kg = self._poly(self.K * self.g)
        self.Kgain = self._poly(self.K * self.gain)
        self.Qh = {k: [self._poly(self.K * (a0 + a1 * tau + (b0 + b1 * tau) * s + (c0 + c1 * tau) * t))
                       for a0, a1, b0, b1, c0, c1 in self.raw[k]] for k in range(4)}
        self.sigma = {k: self._swap_permutation(self.Qh[k]) for k in range(4)}

    @staticmethod
    def _swap_permutation(Q):
        """sigma with Q[i](t, s) = Q[sigma[i]](s, t); must be a fixed-point-free involution."""
        sig = []
        for q in Q:
            sw = expand(q.subs({s: t, t: s}, simultaneous=True))
            hits = [j for j, r in enumerate(Q) if expand(r - sw) == 0]
            if len(hits) != 1:
                raise ValueError("pieces are not closed under the swap s <-> t")
            sig.append(hits[0])
        if any(sig[sig[i]] != i or sig[i] == i for i in range(len(sig))):
            raise ValueError("swap permutation is not a fixed-point-free involution")
        return sig

    @staticmethod
    def _poly(e):
        e = cancel(together(e))
        num, den = fraction(e)
        if Poly(den, y, tau, s, t).total_degree() != 0:
            raise ValueError(f"not a polynomial: {e}")
        return expand(e)


# --- Lean printing ----------------------------------------------------------------------------

VARS = [(y, "y"), (tau, "τ"), (s, "s"), (t, "t"), (s1, "s'"), (t1, "t'"), (tau1, "τ'")]


def lean_rat(c):
    c = Rational(c)
    return f"({c.p}:ℝ)" if c.q == 1 else f"({c.p}/{c.q}:ℝ)"


def lean_poly(e, gens=(y, tau, s, t, s1, t1, tau1)):
    """A polynomial with rational coefficients as a Lean sum of monomials (deterministic order)."""
    e = expand(e)
    if e == 0:
        return "0"
    P = Poly(e, *gens)
    names = dict(VARS)
    out = []
    for mon, c in sorted(P.terms(), key=lambda mc: tuple(-d for d in mc[0])):
        factors = []
        for g_, d in zip(gens, mon):
            if d == 1:
                factors.append(names[g_])
            elif d > 1:
                factors.append(f"{names[g_]} ^ {d}")
        mag = abs(Rational(c))
        body = " * ".join(([lean_rat(mag)] if (mag != 1 or not factors) else []) + factors)
        out.append(("- " if c < 0 else "+ ") + body)
    text = " ".join(out)
    return text[2:] if text.startswith("+ ") else "-" + text[2:] if text.startswith("- ") else text


def nonneg_coeffs_y(e):
    P = Poly(expand(e), y)
    return all(c >= 0 for c in P.all_coeffs())


def bernstein(e):
    """Coefficients b_j(y) with e = sum_j b_j tau^j (1 - tau)^(d - j), d = deg_tau e (exact)."""
    P = Poly(expand(e), tau)
    d = P.degree() if P.degree() > 0 else 0
    a = [P.coeff_monomial(tau**i) for i in range(d + 1)]  # power basis
    # power -> Bernstein: b_j = sum_{i <= j} C(j, i)/C(d, i) a_i, then term b_j C(d, j) tau^j (1-tau)^(d-j)
    b = [expand(sum(Rational(comb(j, i), comb(d, i)) * a[i] for i in range(j + 1)) * comb(d, j)) for j in range(d + 1)]
    assert expand(sum(bj * tau**j * (1 - tau) ** (d - j) for j, bj in enumerate(b)) - expand(e)) == 0
    return d, b


def bern_proof(name, e, strict=False, indent="  "):
    """Lean lines proving `0 ≤ e` (or `0 < e`) for y >= 0, 0 <= tau <= 1.

    Degree 0 in tau: `positivity` (nonnegative coefficients in y). Degree 1: `lin_tau` from the values at
    tau = 0 and tau = 1. Higher degree: a Bernstein expansion (kept for the few tau-quadratic weights,
    because the `ring` rewrite into Bernstein form is the expensive step)."""
    e = expand(e)
    P = Poly(e, tau)
    if P.degree() <= 1 and not strict:
        p0, q0 = expand(P.coeff_monomial(1)), expand(P.coeff_monomial(tau))
        if not (nonneg_coeffs_y(p0) and nonneg_coeffs_y(expand(p0 + q0))):
            raise ValueError(f"{name}: endpoint value with a negative y-coefficient")
        if q0 == 0:
            if p0 == 0:
                return [f"{indent}have {name} : (0:ℝ) ≤ 0 := le_refl 0"]
            return [f"{indent}have {name} : (0:ℝ) ≤ {lean_poly(p0)} := by positivity"]
        one = (f"(by have h : (0:ℝ) ≤ {lean_poly(expand(p0 + q0))} := (by positivity); linarith only [h])"
               if expand(p0 + q0) != 0 else "(by linarith only [])")
        zero = "(by positivity)" if p0 != 0 else "le_rfl"
        return [f"{indent}have {name} : (0:ℝ) ≤ ({lean_poly(p0)}) + ({lean_poly(q0)}) * τ :=",
                f"{indent}  lin_tau hτ0 hτ1 {zero}", f"{indent}    {one}"]
    if P.degree() <= 0 and strict:
        if Poly(e, y).eval(0) <= 0 or not nonneg_coeffs_y(e):
            raise ValueError(f"{name}: not positive")
        return [f"{indent}have {name}' : (0:ℝ) < {lean_poly(e)} := by positivity"]
    d, b = bernstein(e)
    shift = Rational(0)
    if strict and d == 0:
        if Poly(expand(e), y).eval(0) <= 0 or not nonneg_coeffs_y(e):
            raise ValueError(f"{name}: not positive")
        return [f"{indent}have {name}' : (0:ℝ) < {lean_poly(e)} := by positivity"]
    if strict:
        consts = [Poly(bj, y).eval(0) for bj in b]
        shift = min(consts)
        if shift <= 0:
            raise ValueError(f"{name}: no positive Bernstein lower bound")
        b = [expand(bj - shift * comb(d, j)) for j, bj in enumerate(b)]
    if not all(nonneg_coeffs_y(bj) for bj in b):
        raise ValueError(f"{name}: Bernstein coefficient with a negative y-coefficient")
    target = f"({lean_poly(e)}) - {lean_rat(shift)}" if strict else f"{lean_poly(e)}"
    terms = [(j, bj) for j, bj in enumerate(b) if bj != 0]
    if not terms:
        expr_txt, proof = "0", "le_refl _"
    else:
        parts = []
        for j, bj in terms:
            mon = f"({lean_poly(bj)})"
            if j:
                mon += f" * τ ^ {j}"
            if d - j:
                mon += f" * (1 - τ) ^ {d - j}"
            parts.append(mon)
        expr_txt = " + ".join(parts)

        def term(j):
            pf = f"(by positivity : (0:ℝ) ≤ {lean_poly(dict(terms)[j])})"
            if j:
                pf = f"(mul_nonneg {pf} (pow_nonneg hτ0 {j}))"
            if d - j:
                pf = f"(mul_nonneg {pf} (pow_nonneg hσ {d - j}))"
            return pf
        # `a + b + c` is `(a + b) + c`: nest add_nonneg to the left
        proof = term(terms[0][0])
        for j, _ in terms[1:]:
            proof = f"(add_nonneg {proof} {term(j)})"
    if expand(e) == 0 and not strict:
        return [f"{indent}have {name} : (0:ℝ) ≤ 0 := le_refl 0"]
    lines = [f"{indent}have {name} : (0:ℝ) ≤ {target} := by",
             f"{indent}  rw [show {target} = {expr_txt} by ring]",
             f"{indent}  exact {proof}"]
    if strict:
        lines.append(f"{indent}have {name}' : 0 < {lean_poly(e)} := by linarith only [{name}]")
    return lines


# --- candidate lemmas -------------------------------------------------------------------------

def dist_expr(c, j):
    u = (s, t)[j]
    return (1 - u) if c[j] == 1 else u


def weights_y(model, k, weights):
    """Weights rational in (x, mu) -> numerators N_l(y, tau) and common denominator M(y, tau) > 0."""
    lam = {int(li): cancel(together(sympify(w).subs(mu, tau * x ** model.m[k]).subs(x, X))) for li, w in weights.items()}
    M = reduce(lambda a, b: lcm(a, b), [fraction(v)[1] for v in lam.values()])
    N = {li: expand(cancel(v * M)) for li, v in lam.items()}
    M = expand(M)
    if Poly(M, y, tau).coeffs() and all(c < 0 for c in Poly(M, y, tau).coeffs()):
        M, N = -M, {li: -v for li, v in N.items()}
    assert expand(sum(N.values()) - M) == 0
    return N, M


def candidate(model, k, i, c, j, weights, base=False):
    """Data of one candidate: weights, multiplier E, A, B, C and the linear_combination coefficients."""
    kn = (k + 1) % 4
    N, M = weights_y(model, k, weights) if not base else weights_y(model, 0, weights)
    if base:
        q = {0: 2 * model.K * s1, 1: 2 * model.K * t1}[i]  # K V_0(s', t'), tau-free
    else:
        q = model.Qh[k][i].subs({s: s1, t: t1})
    cand = model.Kgain * dist_expr(c, j) + q - model.Kg
    e = 4 if (k == 0 and not base) else 0
    E = (y + 3) ** (1 + e)
    rhs = sum(N[li] * model.Qh[kn][li].subs(tau, tau1) for li in N)
    F = expand(E * (rhs - M * cand))
    sub = {s1: (s + (y + 2) * c[0]) / (y + 3), t1: (t + (y + 2) * c[1]) / (y + 3)}
    sub[tau1] = (1 if base else tau / (y + 3) ** e)
    D = expand(cancel(together(F.subs(sub))))
    PD = Poly(D, s, t)
    if PD.total_degree() > 1 or PD.coeff_monomial(s * t) != 0:
        raise ValueError("D is not affine in (s, t)")
    A, B, C = (expand(PD.coeff_monomial(1)), expand(PD.coeff_monomial(s)), expand(PD.coeff_monomial(t)))
    # F - (A + B s + C t) = e1 ((y+3) s' - s - (y+2) c0) + e2 (...) + e3 ((y+3)^e tau' - tau)
    Fs, Ft, Fu = (expand(F.diff(v)) for v in (s1, t1, tau1))
    e1, e2 = cancel(Fs / (y + 3)), cancel(Ft / (y + 3))
    e3 = cancel(Fu / (y + 3) ** e) if not base else Fu
    for v in (e1, e2, e3):
        if fraction(cancel(v))[1].free_symbols:
            raise ValueError("non-polynomial linear_combination coefficient")
    resid = expand(F - (A + B * s + C * t) - e1 * ((y + 3) * s1 - s - (y + 2) * c[0])
                   - e2 * ((y + 3) * t1 - t - (y + 2) * c[1])
                   - e3 * (((y + 3) ** e * tau1 - tau) if not base else (tau1 - 1)))
    if resid != 0:
        raise ValueError("linear_combination does not close")
    return dict(N=N, M=M, E=E, e=e, A=A, B=B, C=C, e1=expand(e1), e2=expand(e2), e3=expand(e3), cand=cand,
                kn=kn, q=q)


def cand_name(k, i, c, j, base=False):
    return (f"base_{i}_{c[0]}{c[1]}_{j}" if base else f"cand_{k}_{i}_{c[0]}{c[1]}_{j}")


def candidate_lemma(model, k, i, c, j, weights, base=False):
    """The Lean lemma `candS ≤ Mx_{k+1}` of one candidate (see the module docstring)."""
    d = candidate(model, k, i, c, j, weights, base)
    name = cand_name(k, i, c, j, base)
    kn = d["kn"]
    dist = (f"(1 - {'s' if j == 0 else 't'})" if c[j] == 1 else ("s" if j == 0 else "t"))
    src = f"2 * Kc y * {'s' if i == 0 else 't'}'" if base else f"Qh_{k}_{i} y τ s' t'"
    tau_arg = "1" if base else "τ'"
    hyps = ["(hy : 0 ≤ y)"] + ([] if base else ["(hτ0 : 0 ≤ τ)", "(hτ1 : τ ≤ 1)"])
    hyps += ["(hs0 : 0 ≤ s)", "(hs1 : s ≤ 1)", "(ht0 : 0 ≤ t)", "(ht1 : t ≤ 1)",
             f"(hs' : (y + 3) * s' = s + (y + 2) * {c[0]})", f"(ht' : (y + 3) * t' = t + (y + 2) * {c[1]})"]
    if not base:
        hyps.append("(hτ' : (y + 3) ^ 4 * τ' = τ)" if d["e"] == 4 else "(hτ' : τ' = τ)")
    tvars = "{y s t s' t' : ℝ}" if base else "{y τ s t s' t' τ' : ℝ}"
    cand_txt = f"Kgain y * {dist} + {src} - Kg y"
    L = [f"theorem {name} {tvars}", "    " + " ".join(hyps) + " :",
         f"    {cand_txt} ≤ Mx_{kn} y {tau_arg} s t := by"]
    if not base:
        L.append("  have hσ : 0 ≤ 1 - τ := by linarith only [hτ1]")
    N, M = d["N"], d["M"]
    ls = sorted(N)
    rhs = " + ".join(f"({lean_poly(N[li])}) * Qh_{kn}_{li} y {tau_arg} s t" for li in ls)
    lc = [f"({lean_poly(d['e1'])}) * hs'", f"({lean_poly(d['e2'])}) * ht'"]
    if not base:
        lc.append(f"({lean_poly(d['e3'])}) * hτ'")
    unf = sorted({f"Qh_{kn}_{li}" for li in ls} | (set() if base else {f"Qh_{k}_{i}"}) | {"Kgain", "Kg"}
                 | ({"Kc"} if base else set()))
    A, B, C = d["A"], d["B"], d["C"]
    L.append(f"  have hD : ({lean_poly(d['E'])}) * (({rhs}) - ({lean_poly(M)}) * ({cand_txt})) =")
    L.append(f"      ({lean_poly(A)}) + ({lean_poly(B)}) * s + ({lean_poly(C)}) * t := by")
    L.append(f"    unfold {' '.join(unf)}")
    L.append("    linear_combination " + " + ".join(lc))
    L += bern_proof("c00", A)
    L += bern_proof("c10", expand(A + B))
    L += bern_proof("c01", expand(A + C))
    L += bern_proof("c11", expand(A + B + C))
    L.append(f"  have hDn := aff_nonneg hs0 hs1 ht0 ht1 (A := {lean_poly(A)})")
    L.append(f"    (B := {lean_poly(B)}) (C := {lean_poly(C)})")
    L.append("    (by linarith only [c00]) (by linarith only [c10]) (by linarith only [c01])"
             " (by linarith only [c11])")
    L.append("  rw [← hD] at hDn")
    L.append(f"  have hR := nonneg_of_mul_nonneg_right' (by positivity : (0 : ℝ) < {lean_poly(d['E'])}) hDn")
    for li in ls:
        L += bern_proof(f"w{li}", N[li])
        L.append(f"  have p{li} := mul_le_mul_of_nonneg_left (Qh_{kn}_{li}_le y {tau_arg} s t) w{li}")
    L += bern_proof("wM", M, strict=True)
    L.append(f"  have hsum : ({lean_poly(M)}) * Mx_{kn} y {tau_arg} s t = "
             + " + ".join(f"({lean_poly(N[li])}) * Mx_{kn} y {tau_arg} s t" for li in ls) + " := by ring")
    L.append(f"  have hfin : ({lean_poly(M)}) * ({cand_txt}) ≤ ({lean_poly(M)}) * Mx_{kn} y {tau_arg} s t := by")
    L.append("    linarith only [" + ", ".join(["hR", "hsum"] + [f"p{li}" for li in ls]) + "]")
    L.append("  exact le_of_mul_le_mul_left hfin wM'")
    return "\n".join(L)


def mirror_lemma(model, k, i, c, base=False):
    """Coordinate-1 candidate from the coordinate-0 candidate of the swapped piece and corner."""
    name = cand_name(k, i, c, 1, base)
    ri = (1 - i) if base else model.sigma[k][i]
    rep = cand_name(k, ri, (c[1], c[0]), 0, base)
    kn = 1 if base else (k + 1) % 4
    dist = "(1 - t)" if c[1] == 1 else "t"
    src = f"2 * Kc y * {'s' if i == 0 else 't'}'" if base else f"Qh_{k}_{i} y τ s' t'"
    tau_arg = "1" if base else "τ'"
    hyps = ["(hy : 0 ≤ y)"] + ([] if base else ["(hτ0 : 0 ≤ τ)", "(hτ1 : τ ≤ 1)"])
    hyps += ["(hs0 : 0 ≤ s)", "(hs1 : s ≤ 1)", "(ht0 : 0 ≤ t)", "(ht1 : t ≤ 1)",
             f"(hs' : (y + 3) * s' = s + (y + 2) * {c[0]})", f"(ht' : (y + 3) * t' = t + (y + 2) * {c[1]})"]
    if not base:
        hyps.append("(hτ' : (y + 3) ^ 4 * τ' = τ)" if k == 0 else "(hτ' : τ' = τ)")
    tvars = "{y s t s' t' : ℝ}" if base else "{y τ s t s' t' τ' : ℝ}"
    args = ("hy ht0 ht1 hs0 hs1 ht' hs'" if base else "hy hτ0 hτ1 ht0 ht1 hs0 hs1 ht' hs' hτ'")
    rw = [f"Mx_{kn}_swap"] if base else [f"Qh_{k}_{ri}_swap", f"Mx_{kn}_swap"]
    return "\n".join([
        f"theorem {name} {tvars}", "    " + " ".join(hyps) + " :",
        f"    Kgain y * {dist} + {src} - Kg y ≤ Mx_{kn} y {tau_arg} s t := by",
        f"  have h := {rep} (s := t) (t := s) (s' := t') (t' := s') {args}",
        f"  rw [{', '.join(rw)}] at h",
        "  exact h"])


# --- modules ----------------------------------------------------------------------------------

HEADER = """/-
GENERATED by solved/lean_two_pb.py from checks/expected/two-pb-certificates.json; do not edit.
-/
"""


def pieces_module(model):
    L = [HEADER, "import Formal.ICG.TwoPb.Cert", "", "noncomputable section", "", f"namespace {NS}", "",
         "/-- The common denominator `K(y)` of the value-function pieces. -/",
         f"def Kc (y : ℝ) : ℝ := {lean_poly(model.K)}", "",
         "/-- `K g`, `g = 2(1 - x)/(1 + x^2)`, `x = 1/(y + 3)`. -/",
         f"def Kg (y : ℝ) : ℝ := {lean_poly(model.Kg)}", "",
         "/-- `K 2 (1 - x)`. -/",
         f"def Kgain (y : ℝ) : ℝ := {lean_poly(model.Kgain)}", ""]
    for k in range(4):
        for i, q in enumerate(model.Qh[k]):
            L.append(f"/-- Piece {i} of residue {k}, scaled by `K`. -/")
            L.append(f"def Qh_{k}_{i} (y τ s t : ℝ) : ℝ := {lean_poly(q)}")
            L.append("")
        n = len(model.Qh[k])
        body = f"Qh_{k}_{n - 1} y τ s t"
        for i in range(n - 2, -1, -1):
            body = f"max (Qh_{k}_{i} y τ s t) ({body})"
        L.append(f"/-- The maximum of the residue-{k} pieces. -/")
        L.append(f"def Mx_{k} (y τ s t : ℝ) : ℝ := {body}")
        L.append("")
        for i in range(n):
            # leaf i of the right-nested max: Q_i <= max(Q_i, ...) then i times le_max_right
            proof = "le_max_left _ _" if i < n - 1 else "le_rfl"
            for _ in range(i):
                proof = f"({proof}).trans (le_max_right _ _)"
            L.append(f"theorem Qh_{k}_{i}_le (y τ s t : ℝ) : Qh_{k}_{i} y τ s t ≤ Mx_{k} y τ s t := by")
            L.append(f"  unfold Mx_{k}; exact {proof}")
            L.append("")
        hs = " ".join(f"(h{i} : Qh_{k}_{i} y τ s t ≤ c)" for i in range(n))
        body = f"h{n - 1}"
        for i in range(n - 2, -1, -1):
            body = f"max_le h{i} ({body})"
        L += [f"theorem Mx_{k}_le {{y τ s t c : ℝ}} {hs} :", f"    Mx_{k} y τ s t ≤ c := by",
              f"  unfold Mx_{k}; exact {body}", ""]
        sig = model.sigma[k]
        for i in range(n):
            L.append(f"theorem Qh_{k}_{i}_swap (y τ s t : ℝ) : Qh_{k}_{i} y τ t s = Qh_{k}_{sig[i]} y τ s t := by")
            L.append(f"  unfold Qh_{k}_{i} Qh_{k}_{sig[i]}; ring")
            L.append("")
        fwd = " ".join(f"(by rw [Qh_{k}_{i}_swap]; exact Qh_{k}_{sig[i]}_le y τ s t)" for i in range(n))
        bwd = " ".join(f"(by rw [← Qh_{k}_{sig[i]}_swap]; exact Qh_{k}_{sig[i]}_le y τ t s)" for i in range(n))
        L += [f"/-- `Mx_{k}` is symmetric in `(s, t)`. -/",
              f"theorem Mx_{k}_swap (y τ s t : ℝ) : Mx_{k} y τ t s = Mx_{k} y τ s t :=",
              f"  le_antisymm (Mx_{k}_le {fwd})", f"    (Mx_{k}_le {bwd})", ""]
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


CHUNK = 8  # candidate proofs per module: about 1.9 GB per Lean process, so 4 parallel builds fit in 16 GB


def _module(imports, lemmas):
    L = [HEADER] + [f"import {m}" for m in imports] + ["", "set_option linter.unusedVariables false",
                                                       "set_option maxHeartbeats 4000000", "",
                                                       "noncomputable section", "", f"namespace {NS}", ""]
    for lemma in lemmas:
        L += [lemma, ""]
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


def step_modules(model, k, certs):
    """Residue k: chunks `Step{k}_{part}` with the coordinate-0 proofs, then `Step{k}M` with the mirrors."""
    reps = [c for c in certs if c["coord"] == 0]
    mirrors = [c for c in certs if c["coord"] == 1]
    out, names = {}, []
    for part in range(0, len(reps), CHUNK):
        name = f"Step{k}_{part // CHUNK}"
        lemmas = [candidate_lemma(model, k, c["piece"], tuple(c["corner"]), 0, c["weights"])
                  for c in reps[part:part + CHUNK]]
        # each chunk imports the previous one: one build chain per residue, so at most four chunk
        # processes run at once whatever the machine's parallelism
        prev = f"Formal.ICG.TwoPb.{names[-1]}" if names else "Formal.ICG.TwoPb.Pieces"
        out[name] = _module([prev], lemmas)
        names.append(name)
    out[f"Step{k}M"] = _module([f"Formal.ICG.TwoPb.{names[-1]}"],
                               [mirror_lemma(model, k, c["piece"], tuple(c["corner"])) for c in mirrors])
    return out


def base_module(model, certs):
    L = [HEADER, "import Formal.ICG.TwoPb.Pieces", "", "set_option linter.unusedVariables false",
         "set_option maxHeartbeats 4000000", "", "noncomputable section", "", f"namespace {NS}", ""]
    # representatives (coordinate 0) first: a mirror refers to the representative of the swapped piece
    for cert in sorted(certs, key=lambda c: c["coord"]):
        i, c = cert["piece"], tuple(cert["corner"])
        if cert["coord"] == 0:
            L.append(candidate_lemma(model, 0, i, c, 0, cert["weights"], base=True))
        else:
            L.append(mirror_lemma(model, 0, i, c, base=True))
        L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


def render_all(source=SOURCE):
    """All generated modules: {path: text}."""
    data = load(source)
    model = Model(data)
    out = {OUT / "Pieces.lean": pieces_module(model), OUT / "Base.lean": base_module(model, data["base"])}
    for k in range(4):
        certs = [c for c in data["steps"] if c["residue"] == k]
        for name, text in step_modules(model, k, certs).items():
            out[OUT / f"{name}.lean"] = text
    out[OUT / "Steps.lean"] = steps_module(model)
    out[OUT / "Start.lean"] = start_module(model)
    return out


def _dists(c):
    return [("(1 - s)" if c[0] == 1 else "s"), ("(1 - t)" if c[1] == 1 else "t")]


def steps_module(model):
    """`Mx_k_le`, the one-step theorems `step_k_c` and the base theorems `base_c`, assembled from the
    candidate lemmas."""
    L = [HEADER] + [f"import Formal.ICG.TwoPb.Step{k}M" for k in range(4)] + ["import Formal.ICG.TwoPb.Base", "",
         "noncomputable section", "", f"namespace {NS}", ""]
    box = "(hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)"
    for k in range(4):
        kn = (k + 1) % 4
        rel = "(hτ' : (y + 3) ^ 4 * τ' = τ)" if k == 0 else "(hτ' : τ' = τ)"
        for c in CORNERS:
            d = _dists(c)
            args = "hy hτ0 hτ1 hs0 hs1 ht0 ht1 hs' ht' hτ'"
            L.append(f"/-- One step from residue {k}, corner {c}. -/")
            L.append(f"theorem step_{k}_{c[0]}{c[1]} {{y τ s t s' t' τ' : ℝ}} (hy : 0 ≤ y) (hτ0 : 0 ≤ τ) "
                     "(hτ1 : τ ≤ 1)")
            L.append(f"    {box}")
            L.append(f"    (hs' : (y + 3) * s' = s + (y + 2) * {c[0]}) (ht' : (y + 3) * t' = t + (y + 2) * {c[1]})")
            L.append(f"    {rel} :")
            L.append(f"    max (Kgain y * {d[0]}) (Kgain y * {d[1]}) + Mx_{k} y τ s' t' ≤ Kg y + Mx_{kn} y τ' s t := by")
            for j in range(2):
                parts = " ".join(f"(by linarith only [cand_{k}_{i}_{c[0]}{c[1]}_{j} {args}])"
                                 for i in range(len(model.Qh[k])))
                L.append(f"  have h{j} : Mx_{k} y τ s' t' ≤ Kg y + Mx_{kn} y τ' s t - Kgain y * {d[j]} :=")
                L.append(f"    Mx_{k}_le {parts}")
            L.append(f"  rcases le_total (Kgain y * {d[0]}) (Kgain y * {d[1]}) with h | h")
            L.append("  · rw [max_eq_right h]; linarith only [h1]")
            L.append("  · rw [max_eq_left h]; linarith only [h0]")
            L.append("")
    for c in CORNERS:
        d = _dists(c)
        args = "hy hs0 hs1 ht0 ht1 hs' ht'"
        L.append(f"/-- The last step (to `V_0 = 2 max(s, t)`), corner {c}. -/")
        L.append(f"theorem base_{c[0]}{c[1]} {{y s t s' t' : ℝ}} (hy : 0 ≤ y) {box}")
        L.append(f"    (hs' : (y + 3) * s' = s + (y + 2) * {c[0]}) (ht' : (y + 3) * t' = t + (y + 2) * {c[1]}) :")
        L.append(f"    max (Kgain y * {d[0]}) (Kgain y * {d[1]}) + max (2 * Kc y * s') (2 * Kc y * t') ≤")
        L.append("      Kg y + Mx_1 y 1 s t := by")
        for j in range(2):
            L.append(f"  have h{j} : max (2 * Kc y * s') (2 * Kc y * t') ≤ Kg y + Mx_1 y 1 s t - Kgain y * {d[j]} :=")
            L.append(f"    max_le (by linarith only [base_0_{c[0]}{c[1]}_{j} {args}]) "
                     f"(by linarith only [base_1_{c[0]}{c[1]}_{j} {args}])")
        L.append(f"  rcases le_total (Kgain y * {d[0]}) (Kgain y * {d[1]}) with h | h")
        L.append("  · rw [max_eq_right h]; linarith only [h1]")
        L.append("  · rw [max_eq_left h]; linarith only [h0]")
        L.append("")
    abs_lines = ["  have a0 : |(0:ℝ) - s| = s := by rw [zero_sub, abs_neg, abs_of_nonneg hs0]",
                 "  have a1 : |(1:ℝ) - s| = 1 - s := abs_of_nonneg (by linarith only [hs1])",
                 "  have b0 : |(0:ℝ) - t| = t := by rw [zero_sub, abs_neg, abs_of_nonneg ht0]",
                 "  have b1 : |(1:ℝ) - t| = 1 - t := abs_of_nonneg (by linarith only [ht1])",
                 "  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl"]
    order = [(0, 0), (0, 1), (1, 0), (1, 1)]  # rcases order: z = 0, 1 outer; w = 0, 1 inner
    bits = "(hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1)"
    lin = "(hs' : (y + 3) * s' = s + (y + 2) * z) (ht' : (y + 3) * t' = t + (y + 2) * w)"
    for k in range(4):
        kn = (k + 1) % 4
        rel = "(hτ' : (y + 3) ^ 4 * τ' = τ)" if k == 0 else "(hτ' : τ' = τ)"
        L += [f"/-- One step from residue {k}, any corner. -/",
              f"theorem step_{k} {{y τ s t s' t' τ' z w : ℝ}} (hy : 0 ≤ y) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) {box}",
              f"    {bits} {lin} {rel} :",
              f"    max (Kgain y * |z - s|) (Kgain y * |w - t|) + Mx_{k} y τ s' t' ≤ Kg y + Mx_{kn} y τ' s t := by"]
        L += abs_lines
        for c in order:
            L.append(f"  · rw [a{c[0]}, b{c[1]}]; exact step_{k}_{c[0]}{c[1]} hy hτ0 hτ1 hs0 hs1 ht0 ht1 hs' ht' hτ'")
        L.append("")
    L += ["/-- The last step, any corner. -/",
          f"theorem base_any {{y s t s' t' z w : ℝ}} (hy : 0 ≤ y) {box} {bits} {lin} :",
          "    max (Kgain y * |z - s|) (Kgain y * |w - t|) + max (2 * Kc y * s') (2 * Kc y * t') ≤",
          "      Kg y + Mx_1 y 1 s t := by"]
    L += abs_lines
    for c in order:
        L.append(f"  · rw [a{c[0]}, b{c[1]}]; exact base_{c[0]}{c[1]} hy hs0 hs1 ht0 ht1 hs' ht'")
    L.append("")
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"


# --- start identity and attainment ------------------------------------------------------------

# S(b) = b g + alpha + x^b beta_{b mod 4} (formal/Formal/ICG/TwoPb/Sum.lean, `Ssum_closed`)
ALPHA = 2 * (1 + 3 * x**2 - 2 * x**3) / (x**2 + 1) ** 2
BETA = [2 * x**2 * (x**2 + 2 * x - 1) / (x**2 + 1) ** 2, -2 * x**2 * (x**2 - 2 * x - 1) / (x**2 + 1) ** 2,
        -2 * x**2 * (x**2 + 2 * x - 1) / (x**2 + 1) ** 2, 2 * x**2 * (x**2 - 2 * x - 1) / (x**2 + 1) ** 2]
START_N0 = 2  # the start identity holds for b >= 2
# The top-bit-1 maximiser walks the corner 4-cycle: forward for b = 0, 3 (mod 4), reversed otherwise.
FWD = [(0, 0), (0, 1), (1, 1), (1, 0)]
REV = [(1, 1), (0, 1), (0, 0), (1, 0)]


def ks_poly(model, k):
    """KS_k(y, tau) = K (alpha + beta_k x^{m_k} tau): the start bound, as a polynomial."""
    return model._poly(model.K * rat_y(ALPHA + BETA[k] * x ** model.m[k] * tau))


def tau_max_exp(model, k):
    """tau <= (y+3)^(-e) at the start for b >= START_N0, b = k (mod 4)."""
    n = START_N0
    while n % 4 != k:
        n += 1
    return n - model.m[k]


def start_lemmas(model, k):
    ks = ks_poly(model, k)
    e = tau_max_exp(model, k)
    L = []
    tau_h = "(hτ1 : τ ≤ 1)" if e == 0 else f"(hτ1 : (y + 3) ^ {e} * τ ≤ 1)"
    for i, q in enumerate(model.Qh[k]):
        for z in (0, 1):
            diff_ = expand(ks - q.subs({s: z, t: 0}))
            P = Poly(diff_, tau)
            p0, q0 = expand(P.coeff_monomial(1)), expand(P.coeff_monomial(tau))
            if P.degree() > 1:
                raise ValueError("start difference not affine in tau")
            # tau' = (y+3)^e tau in [0, 1]: diff = p0 + (q0 / (y+3)^e) tau'; scale by (y+3)^e
            ps, qs = expand(p0 * (y + 3) ** e), q0
            if not (nonneg_coeffs_y(ps) and nonneg_coeffs_y(expand(ps + qs))):
                raise ValueError(f"start {k} {i} {z}: negative coefficient")
            name = f"start_{k}_{i}_{z}"
            L += [f"theorem {name} {{y τ : ℝ}} (hy : 0 ≤ y) (hτ0 : 0 ≤ τ) {tau_h} :",
                  f"    Qh_{k}_{i} y τ {z} 0 ≤ KS_{k} y τ := by"]
            tt = "τ" if e == 0 else f"((y + 3) ^ {e} * τ)"
            L += [f"  have h0 : (0:ℝ) ≤ {tt} := by positivity",
                  f"  have h := lin_tau h0 hτ1 (p := {lean_poly(ps)}) (q := {lean_poly(qs)})",
                  "    (by positivity) (by have h' : (0:ℝ) ≤ "
                  f"{lean_poly(expand(ps + qs))} := (by positivity); linarith only [h'])"]
            L += [f"  have hE : (0:ℝ) < (y + 3) ^ {e} := by positivity",
                  f"  have key : (y + 3) ^ {e} * (KS_{k} y τ - Qh_{k}_{i} y τ {z} 0) = "
                  f"{lean_poly(ps)} + ({lean_poly(qs)}) * {tt} := by",
                  f"    unfold KS_{k} Qh_{k}_{i}; ring",
                  "  rw [← key] at h",
                  "  linarith only [nonneg_of_mul_nonneg_right' hE h]", ""]
    zs = " ".join(f"(start_{k}_{i}_0 hy hτ0 hτ1)" for i in range(len(model.Qh[k])))
    os_ = " ".join(f"(start_{k}_{i}_1 hy hτ0 hτ1)" for i in range(len(model.Qh[k])))
    L += [f"theorem start_{k} {{y τ z : ℝ}} (hy : 0 ≤ y) (hτ0 : 0 ≤ τ) {tau_h} (hz : z = 0 ∨ z = 1) :",
          f"    Mx_{k} y τ z 0 ≤ KS_{k} y τ := by",
          "  rcases hz with rfl | rfl",
          f"  · exact Mx_{k}_le {zs}", f"  · exact Mx_{k}_le {os_}", ""]
    return L


def attain_data(model):
    """Per (b mod 4, n mod 4): the exact parent identity used along the maximiser at n steps left."""
    def cand_poly(k, i, c, j, base):
        sp, tp = (s + (y + 2) * c[0]) / (y + 3), (t + (y + 2) * c[1]) / (y + 3)
        d = (1 - (s, t)[j]) if c[j] == 1 else (s, t)[j]
        q = (2 * model.K * (sp if i == 0 else tp)) if base else model.Qh[k][i].subs({s: sp, t: tp}, simultaneous=True)
        return expand(cancel(together(model.Kgain * d + q - model.Kg)))

    def target(kn, l_, k, base):
        if base:
            return expand(model.Qh[1][l_].subs(tau, 1))
        return expand(cancel(model.Qh[kn][l_].subs(tau, tau / (y + 3) ** 4 if k == 0 else tau)))

    def parent(kn, l_, c, base):
        """(i, j) with cand_{k,i,c,j} == Qh_{kn,l}: k = kn - 1 (or V_0 for the base)."""
        k = 0 if base else (kn - 1) % 4
        rng = range(2) if base else range(len(model.Qh[k]))
        tl = target(kn, l_, k, base)
        for i in rng:
            for j in range(2):
                if expand(cand_poly(k, i, c, j, base) - tl) == 0:
                    return i, j
        return None

    start_piece = {}
    for k in range(4):
        ks = ks_poly(model, k)
        hits = [i for i, q in enumerate(model.Qh[k]) if expand(q.subs({s: 1, t: 0}) - ks) == 0]
        if not hits:
            raise ValueError(f"no attained start piece for residue {k}")
        start_piece[k] = hits[0]
    table = {}
    for bm in range(4):
        cyc = FWD if bm in (0, 3) else REV
        lnow = start_piece[bm]
        for step in range(4):  # n = bm - step (mod 4), corner cyc[step]
            nm = (bm - step) % 4
            c = cyc[step]
            # n steps left, n = nm (mod 4): the step uses residue nm-1 -> nm
            pij = parent(nm, lnow, c, base=False)
            if pij is None:
                raise ValueError(f"no parent identity (b={bm}, n={nm})")
            table[(bm, nm)] = dict(l=lnow, c=c, i=pij[0], j=pij[1])
            lnow = pij[0]
        if lnow != start_piece[bm]:
            raise ValueError("maximiser pieces are not 4-periodic")
    base = {}
    for bm in range(4):
        cyc = FWD if bm in (0, 3) else REV
        # at n = 1 (n = 1 mod 4) the piece is the one the table assigns to residue 1
        l1 = table[(bm, 2)]["i"]  # the piece at n = 1 is the parent used by the step at n = 2
        c = cyc[(bm - 1) % 4]
        pij = parent(1, l1, c, base=True)
        if pij is None:
            raise ValueError(f"no base identity (b={bm})")
        base[bm] = dict(l=l1, c=c, i=pij[0], j=pij[1])
    return start_piece, table, base


def att_name(k, i, c, j, l_, base=False):
    return (f"att_base_{i}_{c[0]}{c[1]}_{j}" if base else f"att_{k}_{i}_{c[0]}{c[1]}_{j}") + f"_to_{l_}"


def att_lemma(model, k, i, c, j, l_, base=False):
    """`Qh_{k+1,l}(τ'; s, t) = Kgain d_j + Qh_{k,i}(τ; s', t') - Kg`, an exact parent identity."""
    d = candidate(model, k, i, c, j, {str(l_): "1"}, base)
    if any(expand(v) != 0 for v in (d["A"], d["B"], d["C"])):
        raise ValueError("not an exact parent identity")
    kn = 1 if base else (k + 1) % 4
    dist = (f"(1 - {'s' if j == 0 else 't'})" if c[j] == 1 else ("s" if j == 0 else "t"))
    src = f"2 * Kc y * {'s' if i == 0 else 't'}'" if base else f"Qh_{k}_{i} y τ s' t'"
    tau_arg = "1" if base else "τ'"
    hyps = [f"(hs' : (y + 3) * s' = s + (y + 2) * {c[0]})", f"(ht' : (y + 3) * t' = t + (y + 2) * {c[1]})"]
    if not base:
        hyps.append("(hτ' : (y + 3) ^ 4 * τ' = τ)" if d["e"] == 4 else "(hτ' : τ' = τ)")
    tvars = "{y s t s' t' : ℝ}" if base else "{y τ s t s' t' τ' : ℝ}"
    lc = [f"({lean_poly(d['e1'])}) * hs'", f"({lean_poly(d['e2'])}) * ht'"]
    if not base:
        lc.append(f"({lean_poly(d['e3'])}) * hτ'")
    unf = sorted({f"Qh_{kn}_{l_}", "Kgain", "Kg"} | ({"Kc"} if base else {f"Qh_{k}_{i}"}))
    E = lean_poly(d["E"])
    return "\n".join([
        f"theorem {att_name(k, i, c, j, l_, base)} {tvars} (hy : 0 ≤ y) " + " ".join(hyps) + " :",
        f"    Qh_{kn}_{l_} y {tau_arg} s t = Kgain y * {dist} + {src} - Kg y := by",
        f"  have h : ({E}) * (Qh_{kn}_{l_} y {tau_arg} s t - (Kgain y * {dist} + {src} - Kg y)) = 0 := by",
        f"    unfold {' '.join(unf)}",
        "    linear_combination " + " + ".join(lc),
        f"  have hE : ({E}) ≠ 0 := by positivity",
        "  have := (mul_eq_zero.1 h).resolve_left hE",
        "  linarith only [this]"])


def start_module(model):
    """KS_k, the start bounds `start_k`, the equality cases `start_eq_k` and the attainment identities."""
    start_piece, table, base = attain_data(model)
    L = [HEADER, "import Formal.ICG.TwoPb.Pieces", "", "set_option linter.unusedVariables false",
         "set_option maxHeartbeats 4000000", "", "noncomputable section", "", f"namespace {NS}", ""]
    for k in range(4):
        L += [f"/-- `K (α + β_{k} x^{model.m[k]} τ)`: the start bound for `b ≡ {k} (mod 4)`. -/",
              f"def KS_{k} (y τ : ℝ) : ℝ := {lean_poly(ks_poly(model, k))}", ""]
    for k in range(4):
        L += start_lemmas(model, k)
        L += [f"theorem start_eq_{k} (y τ : ℝ) : Qh_{k}_{start_piece[k]} y τ 1 0 = KS_{k} y τ := by",
              f"  unfold Qh_{k}_{start_piece[k]} KS_{k}; ring", ""]
    seen = set()
    for (bm, nm), v in sorted(table.items()):
        key = ((nm - 1) % 4, v["i"], v["c"], v["j"], v["l"])
        if key not in seen:
            seen.add(key)
            L += [att_lemma(model, *key), ""]
    for bm, v in sorted(base.items()):
        key = (0, v["i"], v["c"], v["j"], v["l"])
        if ("base",) + key not in seen:
            seen.add(("base",) + key)
            L += [att_lemma(model, *key, base=True), ""]
    L.append(f"end {NS}")
    return "\n".join(L) + "\n"
