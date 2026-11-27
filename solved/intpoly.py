"""Exact integer polynomials and exact real-root and coefficient-sequence tests.

A polynomial is a tuple of Python integers, ``p[i]`` being the coefficient of ``t**i``.
Tuples are trimmed: the zero polynomial is ``()`` and a nonzero polynomial has a
nonzero last entry. Root counting uses Yun's square-free factorization and Sturm
sequences over the rationals, so every answer is exact.
"""

from fractions import Fraction
from math import comb

ZERO = ()
ONE = (1,)


def trim(coefficients):
    p = list(coefficients)
    while p and p[-1] == 0:
        p.pop()
    return tuple(p)


def poly(coefficients):
    """Validate integer coefficients and return the trimmed tuple."""
    values = tuple(coefficients)
    if any(type(c) is not int for c in values):
        raise TypeError("integer coefficients required")
    return trim(values)


def degree(p):
    return len(p) - 1 if p else -1


def add(p, q):
    if len(p) < len(q):
        p, q = q, p
    out = list(p)
    for i, c in enumerate(q):
        out[i] += c
    return trim(out)


def neg(p):
    return tuple(-c for c in p)


def sub(p, q):
    return add(p, neg(q))


def scale(p, c):
    if c == 0:
        return ZERO
    return tuple(c * a for a in p)


def shift(p, k):
    """Multiply by t**k for k >= 0."""
    if k < 0:
        raise ValueError("nonnegative shift required")
    return (0,) * k + p if p else ZERO


def mul(p, q):
    if not p or not q:
        return ZERO
    out = [0] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                out[i + j] += a * b
    return trim(out)


def reflect(p, n):
    """Return t**n * p(1/t); requires deg p <= n."""
    if degree(p) > n:
        raise ValueError("degree exceeds reflection order")
    return trim(tuple(p[n - i] if 0 <= n - i < len(p) else 0 for i in range(n + 1)))


def truncate(p, bound):
    """Keep the terms of degree < bound."""
    return trim(p[: max(bound, 0)])


def evaluate(p, x):
    value = 0
    for c in reversed(p):
        value = value * x + c
    return value


def is_palindromic(p, n):
    return degree(p) <= n and reflect(p, n) == p


# ---------------------------------------------------------------- coefficient sequences


def has_internal_zeros(p):
    support = [i for i, c in enumerate(p) if c]
    return bool(support) and any(p[i] == 0 for i in range(support[0], support[-1] + 1))


def is_unimodal(p):
    """Weakly increasing then weakly decreasing coefficients (no sign assumption)."""
    i, n = 0, len(p)
    while i + 1 < n and p[i] <= p[i + 1]:
        i += 1
    while i + 1 < n and p[i] >= p[i + 1]:
        i += 1
    return i >= n - 1


def log_concavity_defects(p):
    """Indices i with p[i]**2 < p[i-1] * p[i+1], over the whole coefficient list."""
    return [i for i in range(1, len(p) - 1) if p[i] * p[i] < p[i - 1] * p[i + 1]]


def is_log_concave(p):
    """Log-concave with no internal zeros, the form used in the matroid conjectures."""
    return not has_internal_zeros(p) and not log_concavity_defects(p)


def gamma_vector(p, n):
    """Coefficients g_i with p(t) = sum_i g_i t**i (1+t)**(n-2i), for palindromic p of order n."""
    if not is_palindromic(p, n):
        raise ValueError("polynomial is not palindromic of the stated order")
    rest = list(p) + [0] * (n + 1 - len(p))
    gammas = []
    for i in range(n // 2 + 1):
        g = rest[i]
        gammas.append(g)
        if g:
            for j in range(n - 2 * i + 1):
                rest[i + j] -= g * comb(n - 2 * i, j)
    if any(rest):
        raise ArithmeticError("gamma expansion did not terminate")
    return trim(gammas)


# ---------------------------------------------------------------- exact real roots


def _q(p):
    return [Fraction(c) for c in p]


def _qtrim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def _qdivmod(a, b):
    a = list(a)
    if not b:
        raise ZeroDivisionError("polynomial division by zero")
    out = [Fraction(0)] * max(len(a) - len(b) + 1, 0)
    lead = b[-1]
    while len(a) >= len(b) and a:
        k = len(a) - len(b)
        c = a[-1] / lead
        out[k] = c
        for i, bc in enumerate(b):
            a[i + k] -= c * bc
        _qtrim(a)
    return _qtrim(out), a


def _qderivative(p):
    return _qtrim([i * p[i] for i in range(1, len(p))])


def _qsub(a, b):
    n = max(len(a), len(b))
    return _qtrim([(a[i] if i < len(a) else 0) - (b[i] if i < len(b) else 0) for i in range(n)])


def _qmonic(p):
    lead = p[-1]
    return [c / lead for c in p]


def _qgcd(a, b):
    a, b = _qtrim(list(a)), _qtrim(list(b))
    while b:
        a, b = b, _qdivmod(a, b)[1]
    return _qmonic(a) if a else a


def squarefree_factors(p):
    """Yun's algorithm: [(g_1, 1), (g_2, 2), ...] with p = c * prod g_i**i, g_i square-free."""
    f = _qtrim(_q(p))
    if len(f) <= 1:
        return []
    factors = []
    a = _qgcd(f, _qderivative(f))
    b = _qdivmod(f, a)[0]
    c = _qdivmod(_qderivative(f), a)[0]
    d = _qsub(c, _qderivative(b))
    i = 1
    while len(b) > 1:
        g = _qgcd(b, d)
        if len(g) > 1:
            factors.append((g, i))
        b = _qdivmod(b, g)[0]
        c = _qdivmod(d, g)[0]
        d = _qsub(c, _qderivative(b))
        i += 1
    return factors


def _sturm_chain(f):
    chain = [f, _qderivative(f)]
    while chain[-1] and len(chain[-1]) > 1:
        r = _qdivmod(chain[-2], chain[-1])[1]
        if not r:
            break
        chain.append([-c for c in r])
    return chain


def _sign_changes(values):
    signs = [v > 0 for v in values if v != 0]
    return sum(1 for a, b in zip(signs, signs[1:]) if a != b)


def _signs_at_minus_infinity(chain):
    return [(c[-1] if (len(c) - 1) % 2 == 0 else -c[-1]) for c in chain if c]


def _signs_at_plus_infinity(chain):
    return [c[-1] for c in chain if c]


def _signs_at(chain, x):
    out = []
    for c in chain:
        value = Fraction(0)
        for coefficient in reversed(c):
            value = value * x + coefficient
        out.append(value)
    return out


def _distinct_real_roots(f, low=None, high=None):
    """Distinct real roots of square-free f in (low, high]; None means infinity."""
    chain = _sturm_chain(f)
    left = _signs_at_minus_infinity(chain) if low is None else _signs_at(chain, Fraction(low))
    right = _signs_at_plus_infinity(chain) if high is None else _signs_at(chain, Fraction(high))
    return _sign_changes(left) - _sign_changes(right)


def real_root_count(p, low=None, high=None):
    """Number of real roots of p in (low, high], counted with multiplicity."""
    if not p:
        raise ValueError("the zero polynomial has no finite root count")
    return sum(m * _distinct_real_roots(g, low, high) for g, m in squarefree_factors(p))


def is_real_rooted(p):
    """Every complex root of the nonzero polynomial p is real (constants are real-rooted)."""
    p = poly(p)
    if not p:
        raise ValueError("zero polynomial")
    return real_root_count(p) == degree(p)


def has_only_nonpositive_real_roots(p):
    p = poly(p)
    if not p:
        raise ValueError("zero polynomial")
    return real_root_count(p, None, 0) == degree(p)


def interlaces(f, g):
    """True when f and g are real-rooted and their zeros interlace (in either order).

    Uses the classical criterion: for real-rooted f, g whose degrees differ by at most one,
    the zeros interlace iff the Wronskian f*g' - f'*g does not change sign on the real line,
    i.e. it has no real zero of odd multiplicity. Common zeros are permitted.
    """
    f, g = poly(f), poly(g)
    if not (is_real_rooted(f) and is_real_rooted(g)):
        return False
    if abs(degree(f) - degree(g)) > 1:
        return False
    fd = tuple(i * f[i] for i in range(1, len(f)))
    gd = tuple(i * g[i] for i in range(1, len(g)))
    w = sub(mul(f, gd), mul(fd, g))
    if not w:
        return True
    return all(m % 2 == 0 or _distinct_real_roots(h) == 0 for h, m in squarefree_factors(w))
