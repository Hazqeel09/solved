"""Exact Kazhdan-Lusztig-type polynomials of a matroid from its lattice of flats.

Conventions (standard names: M|F restriction = lower interval [0, F], M/F contraction =
upper interval [F, E]):

* KL polynomial P (Elias-Proudfoot-Wakefield, Thm 2.2): P = 1 in rank 0; otherwise
  deg P < rk/2 and t^rk P(1/t) = sum_F chi_{M|F}(t) P_{M/F}(t).
* Z-polynomial (Proudfoot-Xu-Young, Def 2.1): Z_M(t) = sum_F t^{rk F} P_{M/F}(t).
* Inverse KL polynomial Q (Gao-Xie): with Qhat = (-1)^rk Q, deg Q < rk/2 and
  Qhat_M(t) = sum_F t^{rk F} Qhat_{M|F}(1/t) chi_{M/F}(t)  (Gao-Xie relation (14)).
* Inverse Z-polynomial Y (Gao-Ruan-Xie, eqs. (2)-(3)):
  Y_M(t) = (-1)^rk sum_F (-1)^{rk F} Q_{M|F}(t) t^{rk M - rk F} mu(F, E).
* Chow polynomial (Ferroni-Matherne-Schulte-Vecchi, Thm 1.4): 1 in rank 0, otherwise
  H_M(x) = sum_{F != 0} chibar_{M|F}(x) H_{M/F}(x) with chibar = chi/(x-1).
* Augmented Chow polynomial (FMSV Thm 1.3(iii)): sum_F x^{rk F} H_{M/F}(x).

Every recursion is solved exactly and its defining identity is re-verified; independent
cross-checks (PXY Lemma 2.2 and Gao-Xie Theorem 1.3 (4) for P, palindromicity of Z, Y and
the augmented Chow polynomial, FMSV Prop. 3.7 for the augmented Chow polynomial) raise
ArithmeticError on any mismatch.
"""

from dataclasses import dataclass

from . import intpoly as ip
from .matroid_lattice import interval_characteristic


@dataclass(frozen=True)
class MatroidPolynomials:
    rank: int
    characteristic: tuple
    kl: tuple
    z: tuple
    inverse_kl: tuple
    inverse_z: tuple
    chow: tuple
    augmented_chow: tuple


def _divide_by_t_minus_one(p):
    """Exact quotient p/(t-1); requires p(1) = 0."""
    if ip.evaluate(p, 1) != 0:
        raise ArithmeticError("characteristic polynomial does not vanish at 1")
    out, carry = [], 0
    for c in reversed(p[1:]):
        carry += c
        out.append(carry)
    return ip.trim(tuple(reversed(out)))


def _require(condition, message):
    if not condition:
        raise ArithmeticError(message)


def polynomials(lattice, intervals=None):
    """All invariants of the matroid whose lattice of flats is ``lattice``.

    ``intervals`` may supply precomputed interval characteristic data in the format of
    ``matroid_lattice.interval_characteristic``; by default the reference routine is used.
    """
    chis = interval_characteristic(lattice) if intervals is None else intervals
    ranks = lattice.ranks
    n = len(lattice)
    top = n - 1
    rank = ranks[top]
    _require(len(chis) == n and top in chis[0], "interval data do not match the lattice")

    down = [[] for _ in range(n)]
    for i in range(n):
        for j in chis[i]:
            down[j].append(i)

    # KL polynomials of all contractions M/F, from the top down.
    kl = [None] * n
    kl[top] = ip.ONE
    for i in range(top - 1, -1, -1):
        r = ranks[top] - ranks[i]
        rest = ip.ZERO
        for j, chi in chis[i].items():
            if j != i:
                rest = ip.add(rest, ip.mul(chi, kl[j]))
        p = ip.neg(ip.truncate(rest, (r + 1) // 2))
        _require(ip.reflect(p, r) == ip.add(p, rest), "KL recursion identity failed")
        kl[i] = p

    def z_of(i):
        out = ip.ZERO
        for j in chis[i]:
            out = ip.add(out, ip.shift(kl[j], ranks[j] - ranks[i]))
        return out

    z = z_of(0)
    _require(ip.is_palindromic(z, rank), "Z-polynomial is not palindromic")

    # Inverse KL polynomials of all restrictions M|F, from the bottom up.
    qhat = [None] * n
    qhat[0] = ip.ONE
    for j in range(1, n):
        r = ranks[j]
        rest = ip.ZERO
        for k in down[j]:
            if k != j:
                rest = ip.add(rest, ip.mul(ip.reflect(qhat[k], ranks[k]), chis[k][j]))
        q = ip.truncate(rest, (r + 1) // 2)
        _require(ip.sub(q, ip.reflect(q, r)) == rest, "inverse KL recursion identity failed")
        qhat[j] = q
    inverse = [ip.scale(qhat[j], (-1) ** ranks[j]) for j in range(n)]

    # Cross-checks of P_M: PXY Lemma 2.2 and Gao-Xie Theorem 1.3 (4).
    mu_bottom = {j: chi[0] for j, chi in chis[0].items()}
    via_z = ip.ZERO
    for j, m in mu_bottom.items():
        via_z = ip.add(via_z, ip.scale(ip.shift(z_of(j), ranks[j]), m))
    _require(via_z == kl[0], "P disagrees with PXY Lemma 2.2")
    via_q = ip.ZERO
    for j in chis[0]:
        if j != 0:
            via_q = ip.add(via_q, ip.scale(ip.mul(inverse[j], kl[j]), (-1) ** ranks[j]))
    _require(ip.neg(via_q) == kl[0] or rank == 0, "P disagrees with Gao-Xie Theorem 1.3 (4)")

    # Inverse Z-polynomial.
    yhat = ip.ZERO
    for j in range(n):
        mu_up = chis[j][top][0]
        term = ip.shift(inverse[j], rank - ranks[j])
        yhat = ip.add(yhat, ip.scale(term, (-1) ** ranks[j] * mu_up))
    inverse_z = ip.scale(yhat, (-1) ** rank)
    _require(ip.is_palindromic(inverse_z, rank), "inverse Z-polynomial is not palindromic")

    # Chow polynomials of all contractions.
    chow = [None] * n
    chow[top] = ip.ONE
    for i in range(top - 1, -1, -1):
        h = ip.ZERO
        for j, chi in chis[i].items():
            if j != i:
                h = ip.add(h, ip.mul(_divide_by_t_minus_one(chi), chow[j]))
        _require(ip.degree(h) == ranks[top] - ranks[i] - 1, "Chow polynomial has wrong degree")
        chow[i] = h
    augmented = ip.ZERO
    for j in range(n):
        augmented = ip.add(augmented, ip.shift(chow[j], ranks[j]))
    _require(ip.is_palindromic(augmented, rank), "augmented Chow polynomial is not palindromic")
    prop37 = ip.ONE
    for j in range(n - 1):
        prop37 = ip.add(prop37, ip.shift(chow[j], 1))
    _require(prop37 == augmented, "augmented Chow polynomial disagrees with FMSV Prop. 3.7")

    return MatroidPolynomials(
        rank=rank,
        characteristic=chis[0][top],
        kl=kl[0],
        z=z,
        inverse_kl=inverse[top],
        inverse_z=inverse_z,
        chow=chow[0],
        augmented_chow=augmented,
    )


# ---------------------------------------------------------------- conjecture tests


@dataclass(frozen=True)
class ConjectureReport:
    """Exact truth values of coefficient and root properties of the invariants."""

    kl_real_rooted: bool
    kl_log_concave: bool
    z_real_rooted: bool
    inverse_kl_log_concave: bool
    inverse_z_unimodal: bool
    inverse_z_log_concave: bool
    chow_real_rooted: bool
    augmented_chow_real_rooted: bool

    def open_conjecture_failures(self):
        """Failures of conjectures not refuted in the literature as of 2026-11."""
        names = (
            "z_real_rooted",
            "inverse_z_unimodal",
            "inverse_z_log_concave",
            "chow_real_rooted",
            "augmented_chow_real_rooted",
        )
        return [name for name in names if not getattr(self, name)]


def report(polys):
    return ConjectureReport(
        kl_real_rooted=ip.is_real_rooted(polys.kl),
        kl_log_concave=ip.is_log_concave(polys.kl),
        z_real_rooted=ip.is_real_rooted(polys.z),
        inverse_kl_log_concave=ip.is_log_concave(polys.inverse_kl),
        inverse_z_unimodal=ip.is_unimodal(polys.inverse_z),
        inverse_z_log_concave=ip.is_log_concave(polys.inverse_z),
        chow_real_rooted=ip.is_real_rooted(polys.chow),
        augmented_chow_real_rooted=ip.is_real_rooted(polys.augmented_chow),
    )
