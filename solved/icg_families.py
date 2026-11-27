"""Maximal-energy divisor sets of integral circulant graphs, certified for families of orders.

An order is given as factors ((prime, exponent), ...), where each prime is either the
symbol "p" or "q" (a variable ranging over primes) or a fixed integer prime such as 2 or 3.
For n = prod r_nu^{a_nu}, write divisors d = prod r_nu^{i_nu} (cells) and classes
e = prod r_nu^{alpha_nu}. By multiplicativity of Ramanujan sums,

    E(n, D) = sum_classes w(alpha) |L_alpha(D)|,   L_alpha(D) = sum_{i in D} prod_nu u_nu(alpha_nu, i_nu),
    u_nu(alpha, i) = c(r_nu^alpha, r_nu^(a_nu - i)),  w(alpha) = prod_nu phi(r_nu^(a_nu - alpha_nu)),

with every term an integer polynomial in the symbolic primes (see solved.icg_energy for the
local formulas and the certificate idea). ``certify`` proves that a given family M of
divisor sets consists of maximisers with one common energy polynomial, and that every
other nonempty set has strictly smaller energy, for all real values of the symbolic primes
in [p0, inf) x [q0, inf). Smaller primes are handled separately by exact enumeration.
"""

from dataclasses import dataclass
from functools import cached_property
from itertools import combinations, product

from .icg_energy import (
    P,
    Q,
    _clean,
    certified_positive,
    certified_sign,
    evaluate,
    padd,
    pconst,
    pmul,
    ppow,
    pscale,
)

SYMBOLS = {"p": P, "q": Q}


def _prime_poly(prime):
    if prime in SYMBOLS:
        return SYMBOLS[prime]
    if type(prime) is not int or prime < 2 or any(prime % d == 0 for d in range(2, prime)):
        raise ValueError("fixed primes must be integer primes")
    return pconst(prime)


def _phi_power(r, e):
    if e == 0:
        return pconst(1)
    return padd(ppow(r, e), pscale(ppow(r, e - 1), -1))


def _local(r, alpha, i):
    """c(r^alpha, r^i) as a polynomial in r."""
    if i == 0:
        return pconst(1)
    if i <= alpha:
        return _phi_power(r, i)
    if i == alpha + 1:
        return pscale(ppow(r, i - 1), -1)
    return {}


@dataclass(frozen=True)
class Order:
    factors: tuple

    def __post_init__(self):
        primes = [r for r, _ in self.factors]
        if len(set(primes)) != len(primes) or not self.factors:
            raise ValueError("factors must use distinct primes")
        if any(type(a) is not int or a < 1 for _, a in self.factors):
            raise ValueError("exponents must be positive integers")

    @property
    def cells(self):
        top = tuple(a for _, a in self.factors)
        return tuple(c for c in product(*(range(a + 1) for _, a in self.factors)) if c != top)

    @property
    def classes(self):
        return tuple(product(*(range(a + 1) for _, a in self.factors)))

    @cached_property
    def _tables(self):
        rows, weights = [], []
        for prime, a in self.factors:
            r = _prime_poly(prime)
            rows.append([[_local(r, alpha, a - i) for i in range(a + 1)] for alpha in range(a + 1)])
            weights.append([_phi_power(r, a - alpha) for alpha in range(a + 1)])
        return rows, weights

    def forms(self, cells):
        rows, weights = self._tables
        out = {}
        for cls in self.classes:
            terms = []
            for cell in cells:
                term = pconst(1)
                for nu, (alpha, i) in enumerate(zip(cls, cell)):
                    term = pmul(term, rows[nu][alpha][i])
                terms.append(term)
            w = pconst(1)
            for nu, alpha in enumerate(cls):
                w = pmul(w, weights[nu][alpha])
            out[cls] = (w, padd(*terms))
        return out

    def energy(self, cells, values):
        """Exact energy with the symbolic primes set to ``values`` = {"p": .., "q": ..}."""
        pv, qv = values.get("p", 0), values.get("q", 0)
        return sum(
            evaluate(w, pv, qv) * abs(evaluate(form, pv, qv))
            for w, form in self.forms(cells).values()
        )

    def divisors(self, cells, values):
        out = []
        for cell in cells:
            d = 1
            for (prime, _), i in zip(self.factors, cell):
                d *= (values[prime] if prime in SYMBOLS else prime) ** i
            out.append(d)
        return out


def maximisers_reference(order, values):
    """Reference: all nonempty divisor sets of maximal energy at the given values (exact)."""
    cells = order.cells
    best, arg = None, []
    for r in range(1, len(cells) + 1):
        for subset in combinations(cells, r):
            e = order.energy(subset, values)
            if best is None or e > best:
                best, arg = e, [frozenset(subset)]
            elif e == best:
                arg.append(frozenset(subset))
    return best, arg


@dataclass(frozen=True)
class FamilyCertificate:
    order: Order
    maximisers: tuple
    energy: dict
    region: object
    competitors: int
    inequalities: int


def _signed_energy(forms, p0, q0, require_fixed):
    fixed, free = [], []
    for w, form in forms.values():
        s = certified_sign(form, p0, q0)
        if s is None:
            if require_fixed:
                raise ArithmeticError("a maximiser eigenvalue has no certified constant sign")
            free.append((w, form))
        elif s:
            fixed.append(pscale(pmul(w, form), s))
    return padd(*fixed), free


def certify_reference(order, maximiser_sets, p0=3, q0=3):
    """Reference implementation of ``certify`` (recomputes every form; small orders only)."""
    cells = order.cells
    targets = [frozenset(m) for m in maximiser_sets]
    if not targets or any(not m or not m <= set(cells) for m in targets):
        raise ValueError("maximisers must be nonempty sets of proper-divisor cells")
    star, _ = _signed_energy(order.forms(sorted(targets[0])), p0, q0, require_fixed=True)
    for m in targets[1:]:
        other, _ = _signed_energy(order.forms(sorted(m)), p0, q0, require_fixed=True)
        if other != star:
            raise ArithmeticError("claimed maximisers have different energy polynomials")
    competitors = inequalities = 0
    target_set = set(targets)
    for r in range(1, len(cells) + 1):
        for subset in combinations(cells, r):
            if frozenset(subset) in target_set:
                continue
            competitors += 1
            base, free = _signed_energy(order.forms(subset), p0, q0, require_fixed=False)
            for choice in product((1, -1), repeat=len(free)):
                total = padd(base, *(pscale(pmul(w, f), s) for (w, f), s in zip(free, choice)))
                inequalities += 1
                if not certified_positive(padd(star, pscale(total, -1)), p0, q0):
                    raise ArithmeticError(f"certificate fails for competitor {sorted(subset)}")
    return FamilyCertificate(
        order, tuple(targets), star, rectangle(p0, q0), competitors, inequalities
    )


def parity_set(order, parity):
    """Cells with sum of exponents of the given parity (excluding n itself)."""
    return frozenset(c for c in order.cells if sum(c) % 2 == parity)


@dataclass(frozen=True)
class Region:
    """The image of x, y >= 0 under p = sub_p(x, y), q = sub_q(x, y).

    sub_p and sub_q are polynomials in (x, y) (same dict encoding, x <-> first exponent)
    with nonnegative integer coefficients, so a polynomial in (p, q) whose substituted form
    has nonnegative coefficients is nonnegative on the whole region.
    """

    name: str
    sub_p: tuple
    sub_q: tuple

    def __post_init__(self):
        for sub in (self.sub_p, self.sub_q):
            if any(type(c) is not int or c < 0 for _, c in sub):
                raise ValueError("substitutions need nonnegative integer coefficients")

    def substitute(self, poly):
        sp, sq = dict(self.sub_p), dict(self.sub_q)
        out = {}
        powers_p, powers_q = {0: {(0, 0): 1}}, {0: {(0, 0): 1}}
        for (i, j), c in poly.items():
            for powers, base, e in ((powers_p, sp, i), (powers_q, sq, j)):
                while max(powers) < e:
                    k = max(powers)
                    powers[k + 1] = _clean(pmul(powers[k], base))
            _accumulate(out, pscale(pmul(powers_p[i], powers_q[j]), c), 1)
        return out


def rectangle(p0, q0):
    """p >= p0 and q >= q0."""
    return Region(f"p>={p0}, q>={q0}", (((1, 0), 1), ((0, 0), p0)), (((0, 1), 1), ((0, 0), q0)))


def p_below_q(p0, gap=2):
    """p >= p0 and q >= p + gap (distinct odd primes with p < q satisfy gap = 2)."""
    return Region(
        f"p>={p0}, q>=p+{gap}",
        (((1, 0), 1), ((0, 0), p0)),
        (((1, 0), 1), ((0, 1), 1), ((0, 0), p0 + gap)),
    )


def q_below_p(q0, gap=2):
    """q >= q0 and p >= q + gap."""
    return Region(
        f"q>={q0}, p>=q+{gap}",
        (((0, 1), 1), ((1, 0), 1), ((0, 0), q0 + gap)),
        (((0, 1), 1), ((0, 0), q0)),
    )


# ---------------------------------------------------------------- incremental implementations
#
# Every L_alpha(D) is a sum over the cells of D, and the substitution (p, q) -> (p0 + x, q0 + y)
# is a ring homomorphism. So the shifted forms and the shifted products w * L are maintained
# incrementally while the subsets are visited in Gray-code order (one cell changes per step).


def _gray_walk(m):
    """Yield (subset_bits, toggled_cell, added) for all 2^m - 1 nonempty subsets."""
    bits = 0
    for i in range(1, 1 << m):
        cell = (i & -i).bit_length() - 1
        bits ^= 1 << cell
        yield bits, cell, bool(bits >> cell & 1)


def _accumulate(target, poly, sign):
    for k, v in poly.items():
        total = target.get(k, 0) + sign * v
        if total:
            target[k] = total
        else:
            target.pop(k, None)


def _coefficient_sign(poly):
    if not poly:
        return 0
    values = poly.values()
    if all(v >= 0 for v in values):
        return 1
    if all(v <= 0 for v in values):
        return -1
    return None


def maximisers(order, values):
    """All nonempty divisor sets of maximal energy at the given prime values (exact)."""
    cells = order.cells
    pv, qv = values.get("p", 0), values.get("q", 0)
    forms_by_cell = [order.forms([c]) for c in cells]
    classes = order.classes
    weights = [evaluate(forms_by_cell[0][k][0], pv, qv) for k in classes]
    contrib = [[evaluate(fc[k][1], pv, qv) for k in classes] for fc in forms_by_cell]
    sums = [0] * len(classes)
    best, arg = None, []
    for bits, cell, added in _gray_walk(len(cells)):
        sign = 1 if added else -1
        row = contrib[cell]
        for k in range(len(classes)):
            sums[k] += sign * row[k]
        e = sum(w * abs(x) for w, x in zip(weights, sums))
        if best is None or e > best:
            best, arg = e, [bits]
        elif e == best:
            arg.append(bits)
    sets = [frozenset(c for i, c in enumerate(cells) if b >> i & 1) for b in arg]
    return best, sorted(sets, key=sorted)


def certify(order, maximiser_sets, p0=3, q0=3, region=None):
    """Certify that ``maximiser_sets`` are exactly the maximisers on a region.

    The region defaults to the rectangle [p0, inf) x [q0, inf); any ``Region`` may be given.

    Every claimed maximiser must have certified constant eigenvalue signs and the same
    energy polynomial; every other nonempty set must satisfy E(D*) - E(D) > 0, certified by
    nonnegative shifted coefficients with positive constant term, for every sign choice of
    the eigenvalue forms whose sign is not itself certified. Raises ArithmeticError.
    """
    cells = order.cells
    index = {c: i for i, c in enumerate(cells)}
    targets = [frozenset(m) for m in maximiser_sets]
    if not targets or any(not m or not m <= set(cells) for m in targets):
        raise ValueError("maximisers must be nonempty sets of proper-divisor cells")
    classes = order.classes
    forms_by_cell = [order.forms([c]) for c in cells]
    region = region or rectangle(p0, q0)
    sw = [region.substitute(forms_by_cell[0][k][0]) for k in classes]
    st = [[region.substitute(fc[k][1]) for k in classes] for fc in forms_by_cell]
    swt = [[_clean(pmul(sw[j], st[i][j])) for j in range(len(classes))] for i in range(len(cells))]

    def shifted_state(cell_set):
        sl = [{} for _ in classes]
        wsl = [{} for _ in classes]
        for c in cell_set:
            i = index[c]
            for j in range(len(classes)):
                _accumulate(sl[j], st[i][j], 1)
                _accumulate(wsl[j], swt[i][j], 1)
        return sl, wsl

    star = None
    for m in targets:
        sl, wsl = shifted_state(m)
        energy = {}
        for j in range(len(classes)):
            s = _coefficient_sign(sl[j])
            if s is None:
                raise ArithmeticError("a maximiser eigenvalue has no certified constant sign")
            if s:
                _accumulate(energy, wsl[j], s)
        if star is None:
            star = energy
        elif energy != star:
            raise ArithmeticError("claimed maximisers have different energy polynomials")
    target_bits = {sum(1 << index[c] for c in m) for m in targets}
    sl = [{} for _ in classes]
    wsl = [{} for _ in classes]
    competitors = inequalities = 0
    for bits, cell, added in _gray_walk(len(cells)):
        sign = 1 if added else -1
        for j in range(len(classes)):
            _accumulate(sl[j], st[cell][j], sign)
            _accumulate(wsl[j], swt[cell][j], sign)
        if bits in target_bits:
            continue
        competitors += 1
        base = dict(star)
        free = []
        for j in range(len(classes)):
            s = _coefficient_sign(sl[j])
            if s is None:
                free.append(j)
            elif s:
                _accumulate(base, wsl[j], -s)
        for choice in product((1, -1), repeat=len(free)):
            delta = dict(base)
            for j, s in zip(free, choice):
                _accumulate(delta, wsl[j], -s)
            inequalities += 1
            if not (delta.get((0, 0), 0) > 0 and all(v >= 0 for v in delta.values())):
                subset = sorted(c for i, c in enumerate(cells) if bits >> i & 1)
                raise ArithmeticError(f"certificate fails for competitor {subset}")
    forms = order.forms(sorted(targets[0]))
    st_target = [region.substitute(forms[k][1]) for k in classes]
    energy = padd(
        *(
            pscale(pmul(forms[k][0], forms[k][1]), _coefficient_sign(st_target[j]))
            for j, k in enumerate(classes)
            if _coefficient_sign(st_target[j])
        )
    )
    return FamilyCertificate(order, tuple(targets), energy, region, competitors, inequalities)


def certify_maximum_of(order, candidates, region, weights_grid=8):
    """Certify E(C) < max over ``candidates`` of E(D) on ``region`` for every other set C.

    Each candidate must have certified constant eigenvalue signs on the region, so its
    energy is a polynomial E_D there. For each competitor C and each sign choice of its
    uncertified forms, the certificate finds rational weights lambda >= 0 summing to 1
    (from a grid of step 1/weights_grid over pairs of candidates, including single ones)
    with sum lambda_D E_D - E(C) certified positive; this implies E(C) < max_D E_D.
    Returns (competitors, inequalities); raises ArithmeticError if some competitor fails.
    """
    cand_sets = [frozenset(c) for c in candidates]
    energies = []
    for cells in cand_sets:
        energy = {}
        for w, form in order.forms(sorted(cells)).values():
            s = _coefficient_sign(region.substitute(form))
            if s is None:
                raise ArithmeticError("a candidate eigenvalue has no certified constant sign")
            if s:
                _accumulate(energy, region.substitute(pmul(w, form)), s)
        energies.append(energy)
    mixes = []
    k = len(energies)
    for i in range(k):
        for j in range(i, k):
            for t in range(weights_grid + 1):
                if i == j and t:
                    continue
                mix = {}
                _accumulate(mix, pscale(energies[i], t if i != j else weights_grid), 1)
                if i != j:
                    _accumulate(mix, pscale(energies[j], weights_grid - t), 1)
                mixes.append(mix)
    competitors = inequalities = 0
    for r in range(1, len(order.cells) + 1):
        for cells in combinations(order.cells, r):
            if frozenset(cells) in cand_sets:
                continue
            competitors += 1
            base, free = {}, []
            for w, form in order.forms(cells).values():
                s = _coefficient_sign(region.substitute(form))
                shifted_term = region.substitute(pmul(w, form))
                if s is None:
                    free.append(shifted_term)
                elif s:
                    _accumulate(base, shifted_term, s)
            for choice in product((1, -1), repeat=len(free)):
                energy = dict(base)
                for term, s in zip(free, choice):
                    _accumulate(energy, term, s)
                inequalities += 1
                scaled = pscale(energy, weights_grid)
                for mix in mixes:
                    delta = dict(mix)
                    _accumulate(delta, scaled, -1)
                    if delta.get((0, 0), 0) > 0 and all(v >= 0 for v in delta.values()):
                        break
                else:
                    raise ArithmeticError(f"no convex certificate for competitor {sorted(cells)}")
    return competitors, inequalities


# ---------------------------------------------------------------- deterministic classification

RATIO_SAMPLES = (1.01, 1.05, 1.1, 1.2, 1.3, 1.5, 2, 3, 5, 10)
BASE_SAMPLES = (3, 5, 7, 11, 31, 61, 101, 151)


def _primes(lo, hi, excluded):
    return [
        v
        for v in range(max(lo, 3), hi)
        if all(v % d for d in range(2, int(v**0.5) + 1)) and v not in excluded
    ]


def _next_prime(v):
    v += 1
    while any(v % d == 0 for d in range(2, int(v**0.5) + 1)):
        v += 1
    return v


def _cells_json(sets):
    return sorted([list(map(list, sorted(s))) for s in sets])


def _poly_json(poly):
    return sorted([[i, j, c] for (i, j), c in poly.items()])


def classify(factors, limit=60):
    """Classify the maximisers for an order with one or two symbolic primes (see module doc).

    Symbolic primes range over odd primes different from the fixed ones. Returns a JSON-ready
    dict; every claim in it is backed by an exact certificate or exact enumeration.
    """
    order = Order(tuple(factors))
    fixed = {r for r, _ in order.factors if r not in SYMBOLS}
    symbols = [r for r, _ in order.factors if r in SYMBOLS]
    if symbols == ["p"]:
        primes = _primes(3, limit, fixed)
        _, top = maximisers(order, {"p": primes[-1]})
        for p0 in primes:
            try:
                cert = certify(order, top, region=rectangle(p0, 0))
            except ArithmeticError:
                continue
            small = {str(v): _cells_json(maximisers(order, {"p": v})[1]) for v in primes if v < p0}
            return {
                "kind": "one-symbolic",
                "maximisers": _cells_json(top),
                "certified_from": p0,
                "competitors": cert.competitors,
                "inequalities": cert.inequalities,
                "energy": _poly_json(cert.energy),
                "small_primes": small,
            }
        raise ArithmeticError("no certificate found below the search limit")
    if sorted(symbols) != ["p", "q"]:
        raise ValueError("classify supports one symbolic prime 'p' or two, 'p' and 'q'")
    lo = _primes(3, limit, fixed)[0]
    out = {"kind": "two-symbolic", "smallest_symbolic_prime": lo}
    for name, region in (("p<q", p_below_q(lo)), ("p>q", q_below_p(lo))):
        found = {}
        for base in BASE_SAMPLES:
            for ratio in RATIO_SAMPLES:
                other = _next_prime(int(base * ratio))
                values = {"p": base, "q": other} if name == "p<q" else {"p": other, "q": base}
                if values["p"] in fixed or values["q"] in fixed or min(values.values()) < lo:
                    continue
                for s in maximisers(order, values)[1]:
                    found[s] = True
        candidates = sorted(found, key=sorted)
        try:
            cert = certify(order, candidates, region=region)
            out[name] = {
                "certificate": "exact",
                "maximisers": _cells_json(candidates),
                "competitors": cert.competitors,
                "inequalities": cert.inequalities,
                "energy": _poly_json(cert.energy),
            }
        except ArithmeticError:
            competitors, inequalities = certify_maximum_of(order, candidates, region)
            energies = {}
            for s in candidates:
                energy = {}
                for w, form in order.forms(sorted(s)).values():
                    sign = _coefficient_sign(region.substitute(form))
                    if sign:
                        _accumulate(energy, pmul(w, form), sign)
                energies[s] = energy
            out[name] = {
                "certificate": "maximum-of-candidates",
                "candidates": _cells_json(candidates),
                "candidate_energies": [_poly_json(energies[s]) for s in candidates],
                "competitors": competitors,
                "inequalities": inequalities,
            }
    return out
