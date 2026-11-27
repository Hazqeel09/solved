"""Exact invariants of q-uniform matroids with free points, by recursion on parameters.

F(n, k, m) denotes the rank-k truncation T_k(PG(n-1, q)) of the projective geometry,
extended by m points in general position (iterated free extensions); F(n, k, 0) is the
q-uniform matroid and q = 1 gives the uniform matroid U_{k, n+m}.

Every proper flat of F(n, k, m) is X + A with X a subspace of GF(q)^n of dimension x, A a
set of a free points, and x + a <= k - 1; its rank is x + a. Free points lie in no proper
flat except those containing them, so these sets are closed. Consequently

* the lower interval [0, X + A] is PG(x-1, q) x B_a (subspace lattice times Boolean),
* the upper interval [X + A, E] is F(n - x, k - x - a, m - a) (contracting a free point of a
  free extension truncates by one rank, and contraction by X commutes with free extension),
* a flat of type (x, a) lies below [n-x, x'-x]_q binom(m-a, a'-a) flats of type (x', a').

Each recursion of ``solved.matroid_polynomials`` therefore reduces to one over (n, k, m).
The tests compare every invariant with the lattice-of-flats engine on uniform matroids,
truncated projective geometries and their explicit free extensions.
"""

from dataclasses import dataclass
from functools import lru_cache
from math import comb

from . import intpoly as ip
from .matroid_polynomials import MatroidPolynomials, _divide_by_t_minus_one


def gaussian(n, k, q):
    if not 0 <= k <= n:
        return 0
    num = den = 1
    for i in range(k):
        if q == 1:
            num *= n - i
            den *= i + 1
        else:
            num *= q ** (n - i) - 1
            den *= q ** (i + 1) - 1
    return num // den


def _pg_characteristic(j, q):
    """chi of the subspace lattice of GF(q)^j: prod_{i<j} (t - q^i)."""
    out = ip.ONE
    for i in range(j):
        out = ip.mul(out, (-(q**i), 1))
    return out


@dataclass(frozen=True)
class QUniform:
    q: int

    def __post_init__(self):
        if type(self.q) is not int or self.q < 1:
            raise ValueError("q must be a positive integer (1 gives uniform matroids)")

    def _check(self, n, k, m):
        if any(type(v) is not int for v in (n, k, m)) or not (0 <= k <= n and m >= 0):
            raise ValueError("need 0 <= k <= n and m >= 0")

    def types(self, n, k, m):
        """(x, a, count) for the proper flats X + A of F(n, k, m)."""
        self._check(n, k, m)
        out = []
        for x in range(min(n, k - 1) + 1):
            for a in range(min(m, k - 1 - x) + 1):
                out.append((x, a, gaussian(n, x, self.q) * comb(m, a)))
        return out

    def _lower_mobius(self, x, a):
        return (-1) ** (x + a) * self.q ** (x * (x - 1) // 2)

    def _lower_characteristic(self, x, a):
        return ip.mul(_pg_characteristic(x, self.q), ip.ONE if a == 0 else _power((-1, 1), a))

    @lru_cache(maxsize=None)  # noqa: B019 - the instance is immutable and hashable
    def characteristic(self, n, k, m=0):
        self._check(n, k, m)
        if k == 0:
            return ip.ONE
        out = ip.ZERO
        for x, a, count in self.types(n, k, m):
            term = ip.shift(ip.ONE, k - x - a)
            out = ip.add(out, ip.scale(term, count * self._lower_mobius(x, a)))
        return ip.add(out, (-ip.evaluate(out, 1),))  # chi(1) = 0 fixes mu(0, E)

    def mobius(self, n, k, m=0):
        return self.characteristic(n, k, m)[0] if k else 1

    @lru_cache(maxsize=None)  # noqa: B019
    def kl(self, n, k, m=0):
        self._check(n, k, m)
        if k == 0:
            return ip.ONE
        rest = self.characteristic(n, k, m)
        for x, a, count in self.types(n, k, m):
            if x + a:
                term = ip.mul(self._lower_characteristic(x, a), self.kl(n - x, k - x - a, m - a))
                rest = ip.add(rest, ip.scale(term, count))
        p = ip.neg(ip.truncate(rest, (k + 1) // 2))
        if ip.reflect(p, k) != ip.add(p, rest):
            raise ArithmeticError("KL recursion identity failed")
        return p

    def z(self, n, k, m=0):
        out = ip.shift(ip.ONE, k)
        for x, a, count in self.types(n, k, m):
            out = ip.add(out, ip.scale(ip.shift(self.kl(n - x, k - x - a, m - a), x + a), count))
        return out

    @lru_cache(maxsize=None)  # noqa: B019
    def inverse_kl_hat(self, n, k, m=0):
        self._check(n, k, m)
        if k == 0:
            return ip.ONE
        rest = ip.ZERO
        for x, a, count in self.types(n, k, m):
            # Qhat of PG(x-1) x B_a is the constant (-1)^(x+a) q^C(x,2); t^(x+a) Qhat(1/t).
            lower = ip.shift((self._lower_mobius(x, a),), x + a)
            term = ip.mul(lower, self.characteristic(n - x, k - x - a, m - a))
            rest = ip.add(rest, ip.scale(term, count))
        q = ip.truncate(rest, (k + 1) // 2)
        if ip.sub(q, ip.reflect(q, k)) != rest:
            raise ArithmeticError("inverse KL recursion identity failed")
        return q

    def inverse_kl(self, n, k, m=0):
        return ip.scale(self.inverse_kl_hat(n, k, m), (-1) ** k)

    def inverse_z(self, n, k, m=0):
        yhat = ip.scale(self.inverse_kl(n, k, m), (-1) ** k)
        for x, a, count in self.types(n, k, m):
            q_lower = self.q ** (x * (x - 1) // 2)
            coefficient = (-1) ** (x + a) * q_lower * self.mobius(n - x, k - x - a, m - a)
            yhat = ip.add(yhat, ip.scale(ip.shift(ip.ONE, k - x - a), coefficient * count))
        return ip.scale(yhat, (-1) ** k)

    @lru_cache(maxsize=None)  # noqa: B019
    def chow(self, n, k, m=0):
        self._check(n, k, m)
        if k == 0:
            return ip.ONE
        out = _divide_by_t_minus_one(self.characteristic(n, k, m))
        for x, a, count in self.types(n, k, m):
            if x + a:
                lower = _divide_by_t_minus_one(self._lower_characteristic(x, a))
                term = ip.mul(lower, self.chow(n - x, k - x - a, m - a))
                out = ip.add(out, ip.scale(term, count))
        return out

    def augmented_chow(self, n, k, m=0):
        out = ip.shift(ip.ONE, k)
        for x, a, count in self.types(n, k, m):
            term = ip.shift(self.chow(n - x, k - x - a, m - a), x + a)
            out = ip.add(out, ip.scale(term, count))
        return out

    def polynomials(self, n, k, m=0):
        polys = MatroidPolynomials(
            rank=k,
            characteristic=self.characteristic(n, k, m),
            kl=self.kl(n, k, m),
            z=self.z(n, k, m),
            inverse_kl=self.inverse_kl(n, k, m),
            inverse_z=self.inverse_z(n, k, m),
            chow=self.chow(n, k, m),
            augmented_chow=self.augmented_chow(n, k, m),
        )
        for name in ("z", "inverse_z", "augmented_chow"):
            if not ip.is_palindromic(getattr(polys, name), k):
                raise ArithmeticError(f"{name} is not palindromic")
        return polys


def _power(p, e):
    out = ip.ONE
    for _ in range(e):
        out = ip.mul(out, p)
    return out
