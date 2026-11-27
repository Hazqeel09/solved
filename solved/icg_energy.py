"""Exact certificate for the energy-maximising divisor set of ICG(p^2 q^3, D).

Setting (Roldan, arXiv:2604.09491). The integral circulant graph ICG(n, D) has vertex set
Z_n, with a ~ b iff gcd(a - b, n) lies in the nonempty set D of proper divisors of n. Its
eigenvalues are lambda_j = sum_{d in D} c(j, n/d), where c is the Ramanujan sum. The energy
is E(n, D) = sum_{e | n} phi(n/e) |sum_{d in D} c(e, n/d)|.

For n = p^2 q^3 write d = p^a q^b and e = p^alpha q^beta. Since c(e, .) is multiplicative
in its second argument, c(e, n/d) = u_alpha(a) v_beta(b) with local Ramanujan sums
u_alpha(a) = c(p^alpha, p^(2-a)) and v_beta(b) = c(q^beta, q^(3-b)). Hence

    E(D) = sum_{alpha, beta} w_{alpha beta} |L_{alpha beta}(D)|,
    L_{alpha beta}(D) = sum_{(a,b) in D} u_alpha(a) v_beta(b),
    w_{alpha beta} = phi(p^(2-alpha)) phi(q^(3-beta)),

where every u, v and w is an integer polynomial in (p, q). Because |L| = max(L, -L),
E(D*) > E(D) holds at (p, q) iff E(D*) - sum w s L(D) > 0 for every sign vector s. The
module proves this for every D != D* and every real p, q >= 3 by exact polynomial
certificates. A polynomial in (p, q) is certified nonnegative (resp. positive) on
[p0, inf) x [q0, inf) when, after substituting p = p0 + x and q = q0 + y, all its
coefficients are >= 0 (and its constant term is > 0).

Signs of the linear forms L(D) are fixed by the same test where possible; each remaining
form is branched over both signs, which is sound because the true sign at any point is one
of the two. All arithmetic is exact over the integers.
"""

from dataclasses import dataclass
from itertools import combinations, product
from math import comb, gcd

# Bivariate integer polynomials: dict {(i, j): c} meaning c * p**i * q**j, zero terms removed.


def _clean(poly):
    return {k: v for k, v in poly.items() if v}


def padd(*polys):
    out = {}
    for poly in polys:
        for k, v in poly.items():
            out[k] = out.get(k, 0) + v
    return _clean(out)


def pscale(poly, c):
    return _clean({k: c * v for k, v in poly.items()})


def pmul(a, b):
    out = {}
    for (i, j), u in a.items():
        for (k, m), v in b.items():
            out[(i + k, j + m)] = out.get((i + k, j + m), 0) + u * v
    return _clean(out)


def pconst(c):
    return _clean({(0, 0): c})


P = {(1, 0): 1}
Q = {(0, 1): 1}


def ppow(poly, e):
    out = pconst(1)
    for _ in range(e):
        out = pmul(out, poly)
    return out


def evaluate(poly, pv, qv):
    return sum(c * pv**i * qv**j for (i, j), c in poly.items())


def shifted(poly, p0, q0):
    """Coefficients of poly(p0 + x, q0 + y) as a dict over monomials x^k y^m."""
    out = {}
    for (i, j), c in poly.items():
        for k in range(i + 1):
            for m in range(j + 1):
                key = (k, m)
                out[key] = out.get(key, 0) + c * comb(i, k) * p0 ** (i - k) * comb(j, m) * q0 ** (
                    j - m
                )
    return _clean(out)


def certified_sign(poly, p0, q0):
    """+1 / -1 when poly is certified >= 0 / <= 0 on the shifted quadrant, 0 if identically
    zero, None when the coefficient test is inconclusive."""
    if not poly:
        return 0
    coeffs = shifted(poly, p0, q0).values()
    if all(c >= 0 for c in coeffs):
        return 1
    if all(c <= 0 for c in coeffs):
        return -1
    return None


def certified_positive(poly, p0, q0):
    s = shifted(poly, p0, q0)
    return s.get((0, 0), 0) > 0 and all(c >= 0 for c in s.values())


# ---------------------------------------------------------------- the energy model


def _phi_prime_power(var, exponent):
    """phi(var^exponent) as a polynomial: var^e - var^(e-1) for e >= 1, and 1 for e = 0."""
    if exponent == 0:
        return pconst(1)
    return padd(ppow(var, exponent), pscale(ppow(var, exponent - 1), -1))


def _local_ramanujan(var, alpha, i):
    """c(var^alpha, var^i) for a prime var, as a polynomial in var."""
    if i == 0:
        return pconst(1)
    if i <= alpha:
        return _phi_prime_power(var, i)
    if i == alpha + 1:
        return pscale(ppow(var, i - 1), -1)
    return {}


U = [[_local_ramanujan(P, alpha, 2 - a) for a in range(3)] for alpha in range(3)]
V = [[_local_ramanujan(Q, beta, 3 - b) for b in range(4)] for beta in range(4)]
WEIGHT = [
    [pmul(_phi_prime_power(P, 2 - alpha), _phi_prime_power(Q, 3 - beta)) for beta in range(4)]
    for alpha in range(3)
]
CELLS = tuple((a, b) for a in range(3) for b in range(4) if (a, b) != (2, 3))
STAR = frozenset({(0, 0), (2, 0), (1, 1), (0, 2), (2, 2), (1, 3)})  # 1, p^2, pq, q^2, p^2q^2, pq^3
CLASSES = tuple((alpha, beta) for alpha in range(3) for beta in range(4))


def linear_forms(cells):
    """L_{alpha beta}(D) for the divisor set D = {p^a q^b : (a, b) in cells}."""
    return {
        (alpha, beta): padd(*(pmul(U[alpha][a], V[beta][b]) for a, b in cells))
        for alpha, beta in CLASSES
    }


def energy(cells, pv, qv):
    """Exact energy at integer (p, q) from the factorized model."""
    forms = linear_forms(cells)
    return sum(
        evaluate(WEIGHT[al][be], pv, qv) * abs(evaluate(forms[(al, be)], pv, qv))
        for al, be in CLASSES
    )


def star_energy_polynomial(p0=3, q0=3):
    forms = linear_forms(STAR)
    terms = []
    for key in CLASSES:
        s = certified_sign(forms[key], p0, q0)
        if s not in (1, -1):
            raise ArithmeticError(f"sign of the D* eigenvalue at class {key} is not certified")
        terms.append(pscale(pmul(WEIGHT[key[0]][key[1]], forms[key]), s))
    return padd(*terms)


# ---------------------------------------------------------------- the proof


@dataclass(frozen=True)
class Certificate:
    p0: int
    q0: int
    divisor_sets: int
    branched_forms: int
    inequalities: int


def prove(p0=3, q0=3):
    """Certify E(D*) > E(D) for every nonempty D != D* on [p0, inf) x [q0, inf).

    Raises ArithmeticError naming the first divisor set whose certificate fails.
    """
    star = star_energy_polynomial(p0, q0)
    sets = branched = inequalities = 0
    for r in range(1, len(CELLS) + 1):
        for cells in combinations(CELLS, r):
            if frozenset(cells) == STAR:
                continue
            sets += 1
            forms = linear_forms(cells)
            fixed, free = [], []
            for key in CLASSES:
                s = certified_sign(forms[key], p0, q0)
                if s is None:
                    free.append(key)
                else:
                    fixed.append((key, s))
            branched += len(free)
            base = padd(*(pscale(pmul(WEIGHT[k[0]][k[1]], forms[k]), s) for k, s in fixed if s))
            for choice in product((1, -1), repeat=len(free)):
                total = padd(
                    base,
                    *(pscale(pmul(WEIGHT[k[0]][k[1]], forms[k]), s) for k, s in zip(free, choice)),
                )
                inequalities += 1
                if not certified_positive(padd(star, pscale(total, -1)), p0, q0):
                    raise ArithmeticError(f"certificate fails for D = {sorted(cells)}")
    return Certificate(p0, q0, sets, branched, inequalities)


# ---------------------------------------------------------------- independent definition


def _factor(m):
    out, d = {}, 2
    while d * d <= m:
        while m % d == 0:
            out[d] = out.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        out[m] = out.get(m, 0) + 1
    return out


def _mobius(m):
    f = _factor(m)
    return 0 if any(e > 1 for e in f.values()) else (-1) ** len(f)


def _totient(m):
    out = m
    for prime in _factor(m):
        out = out // prime * (prime - 1)
    return out


def ramanujan(j, m):
    """c(j, m) = mu(m/g) phi(m) / phi(m/g) with g = gcd(j, m) (Holder's formula)."""
    g = gcd(j, m)
    return _mobius(m // g) * _totient(m) // _totient(m // g)


def direct_energy(n, divisors):
    """E(n, D) = sum_{e | n} phi(n/e) |sum_{d in D} c(e, n/d)| straight from the definition."""
    divs = [e for e in range(1, n + 1) if n % e == 0]
    return sum(_totient(n // e) * abs(sum(ramanujan(e, n // d) for d in divisors)) for e in divs)
