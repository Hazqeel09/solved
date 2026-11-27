"""Lattices of flats of finite matroids, built exactly from closure operators.

Flats are bitmasks over the ground set ``range(size)``. A ``FlatLattice`` stores its
flats sorted by rank (ties by bitmask), so index 0 is the closure of the empty set and the
last index is the ground set. Every constructor goes through a closure operator or an
explicit subspace enumeration whose output is validated, so the stored family is the full
lattice of flats of a genuine matroid.

The interval data used by the polynomial invariants are the characteristic polynomials
chi_[F,G](t) = sum_{F <= H <= G} mu(F, H) t^(rk G - rk H) of every interval. Its constant
term is mu(F, G). ``interval_characteristic`` computes them in pure Python; it is the
reference oracle for any accelerated backend.
"""

from dataclasses import dataclass
from itertools import combinations, product

from .intpoly import trim


@dataclass(frozen=True)
class FlatLattice:
    size: int
    flats: tuple
    ranks: tuple

    def __post_init__(self):
        if len(self.flats) != len(self.ranks) or not self.flats:
            raise ValueError("flats and ranks must be nonempty and aligned")
        if list(self.ranks) != sorted(self.ranks):
            raise ValueError("flats must be sorted by rank")
        full = (1 << self.size) - 1
        if self.flats[-1] != full or self.ranks[0] != 0 or self.ranks.count(0) != 1:
            raise ValueError("lattice must run from a unique rank-zero flat to the ground set")

    @property
    def rank(self):
        return self.ranks[-1]

    def __len__(self):
        return len(self.flats)


def _bit(e):
    return 1 << e


def _members(mask):
    out, e = [], 0
    while mask:
        if mask & 1:
            out.append(e)
        mask >>= 1
        e += 1
    return out


def validate(lattice):
    """Check the flat axioms exhaustively: E is a flat, flats are closed under intersection,
    the covers of every flat partition its complement, and ranks increase by one along covers.
    Quadratic in the number of flats; intended for tests and moderate lattices."""
    flats = set(lattice.flats)
    rank_of = dict(zip(lattice.flats, lattice.ranks))
    full = (1 << lattice.size) - 1
    if full not in flats:
        raise ValueError("ground set is not a flat")
    ordered = list(lattice.flats)
    for i, a in enumerate(ordered):
        for b in ordered[i + 1 :]:
            if a & b not in flats:
                raise ValueError("flats are not closed under intersection")
    for f in ordered:
        above = [g for g in ordered if g != f and g & f == f]
        covers = [
            g
            for g in above
            if not any(h != g and h & g == h and h & f == f and h != f for h in above)
        ]
        union = 0
        for g in covers:
            if (g & ~f) & union:
                raise ValueError("covers of a flat overlap outside it")
            if rank_of[g] != rank_of[f] + 1:
                raise ValueError("rank does not increase by one along a cover")
            union |= g & ~f
        if union != full & ~f:
            raise ValueError("covers of a flat do not partition its complement")


def from_closure(size, closure):
    """Build the lattice of flats from a closure operator on bitmasks.

    Flats of rank i+1 are exactly the closures cl(F + e) of rank-i flats F and e outside F,
    so a breadth-first pass enumerates the lattice. Covering pairs are checked to satisfy
    the matroid cover-partition property (the covers of F partition the complement of F).
    """
    if type(size) is not int or size < 0:
        raise ValueError("ground-set size must be a nonnegative integer")
    full = (1 << size) - 1
    bottom = closure(0)
    level, ranks_of = {bottom}, {bottom: 0}
    rank = 0
    while level:
        nxt = set()
        for flat in level:
            covered = 0
            seen = set()
            for e in range(size):
                if flat >> e & 1 or covered >> e & 1:
                    continue
                cover = closure(flat | _bit(e))
                if cover & flat != flat or cover == flat:
                    raise ValueError("closure is not extensive/increasing on this input")
                if cover in seen:
                    raise ValueError("closure violates the cover-partition axiom")
                seen.add(cover)
                if (cover & ~flat) & covered:
                    raise ValueError("covers of a flat overlap outside it: not a matroid")
                covered |= cover & ~flat
                nxt.add(cover)
            if covered != full & ~flat:
                raise ValueError("covers of a flat do not partition its complement")
        rank += 1
        for flat in nxt:
            if flat in ranks_of:
                raise ValueError("a flat appeared at two ranks: closure is not a matroid closure")
            ranks_of[flat] = rank
        level = nxt
    order = sorted(ranks_of, key=lambda f: (ranks_of[f], f))
    if order[-1] != full:
        raise ValueError("ground set is not the top flat")
    return FlatLattice(size, tuple(order), tuple(ranks_of[f] for f in order))


def from_rank_function(size, rank):
    def closure(mask):
        r = rank(mask)
        out = mask
        for e in range(size):
            if not mask >> e & 1 and rank(mask | _bit(e)) == r:
                out |= _bit(e)
        return out

    return from_closure(size, closure)


def from_bases(size, bases):
    """Matroid given by a nonempty list of bases (iterables of elements)."""
    masks = {sum(_bit(e) for e in b) for b in bases}
    if not masks:
        raise ValueError("at least one basis required")
    if len({m.bit_count() for m in masks}) != 1:
        raise ValueError("bases must have equal size")
    masks = tuple(masks)

    def rank(mask):
        return max((m & mask).bit_count() for m in masks)

    return from_rank_function(size, rank)


def uniform(k, n):
    if not 0 <= k <= n:
        raise ValueError("uniform matroid needs 0 <= k <= n")
    full = (1 << n) - 1
    return from_closure(n, lambda mask: mask if mask.bit_count() < k else full)


def boolean(n):
    return uniform(n, n)


def graphic(num_vertices, edges):
    """Cycle matroid of a multigraph; loops (u == v) are allowed."""
    edges = [tuple(e) for e in edges]
    if any(not (0 <= u < num_vertices and 0 <= v < num_vertices) for u, v in edges):
        raise ValueError("edge endpoint out of range")

    def closure(mask):
        parent = list(range(num_vertices))

        def find(x):
            while parent[x] != x:
                parent[x] = parent[parent[x]]
                x = parent[x]
            return x

        for e in _members(mask):
            u, v = edges[e]
            parent[find(u)] = find(v)
        out = 0
        for e, (u, v) in enumerate(edges):
            if find(u) == find(v):
                out |= _bit(e)
        return out

    return from_closure(len(edges), closure)


def complete_graph(n):
    return graphic(n, list(combinations(range(n), 2)))


def paving(size, rank, big_hyperplanes):
    """Paving matroid of the given rank whose hyperplanes of size >= rank are listed.

    The listed sets must pairwise meet in at most rank-2 elements; the remaining
    (rank-1)-subsets not covered by a listed hyperplane are hyperplanes too.
    """
    big = [sum(_bit(e) for e in h) for h in big_hyperplanes]
    if rank < 1 or any(h.bit_count() < rank for h in big):
        raise ValueError("listed hyperplanes must have at least rank elements")
    for a, b in combinations(big, 2):
        if (a & b).bit_count() > rank - 2:
            raise ValueError("two listed hyperplanes share a (rank-1)-subset")
    full = (1 << size) - 1

    def closure(mask):
        c = mask.bit_count()
        if c <= rank - 2:
            return mask
        if c == rank - 1:
            for h in big:
                if h & mask == mask:
                    return h
            return mask
        for h in big:
            if h & mask == mask:
                return h
        return full

    return from_closure(size, closure)


# ---------------------------------------------------------------- linear matroids over GF(p)


def _check_prime(p):
    if type(p) is not int or p < 2 or any(p % d == 0 for d in range(2, int(p**0.5) + 1)):
        raise ValueError("a prime field order is required")


def _rank_mod_p(rows, p):
    rows = [list(r) for r in rows]
    rank, col = 0, 0
    width = len(rows[0]) if rows else 0
    while rank < len(rows) and col < width:
        pivot = next((i for i in range(rank, len(rows)) if rows[i][col] % p), None)
        if pivot is None:
            col += 1
            continue
        rows[rank], rows[pivot] = rows[pivot], rows[rank]
        inv = pow(rows[rank][col], -1, p)
        rows[rank] = [x * inv % p for x in rows[rank]]
        for i in range(len(rows)):
            if i != rank and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(x - f * y) % p for x, y in zip(rows[i], rows[rank])]
        rank += 1
        col += 1
    return rank


def linear(vectors, p):
    """Vector matroid of the given columns over the prime field GF(p)."""
    _check_prime(p)
    vectors = [tuple(int(x) % p for x in v) for v in vectors]

    def rank(mask):
        rows = [vectors[e] for e in _members(mask)]
        return _rank_mod_p(rows, p) if rows else 0

    return from_rank_function(len(vectors), rank)


def normalize(vector, p):
    """Projective representative: first nonzero coordinate scaled to 1."""
    v = tuple(int(x) % p for x in vector)
    lead = next((x for x in v if x), None)
    if lead is None:
        raise ValueError("the zero vector is not a projective point")
    inv = pow(lead, -1, p)
    return tuple(x * inv % p for x in v)


def projective_points(r, p):
    _check_prime(p)
    return sorted({normalize(v, p) for v in product(range(p), repeat=r) if any(v)})


def _rref_subspaces(r, p):
    """Yield a basis (tuple of rows) for every subspace of GF(p)^r, once each."""
    yield ()
    for d in range(1, r + 1):
        for pivots in combinations(range(r), d):
            free = [(i, c) for i in range(d) for c in range(pivots[i] + 1, r) if c not in pivots]
            for values in product(range(p), repeat=len(free)):
                rows = [[0] * r for _ in range(d)]
                for i, c in enumerate(pivots):
                    rows[i][c] = 1
                for (i, c), x in zip(free, values):
                    rows[i][c] = x
                yield tuple(tuple(row) for row in rows)


def _span_points(basis, p):
    pts = set()
    for coeffs in product(range(p), repeat=len(basis)):
        if any(coeffs):
            v = [0] * len(basis[0])
            for c, row in zip(coeffs, basis):
                if c:
                    for j, x in enumerate(row):
                        v[j] = (v[j] + c * x) % p
            pts.add(normalize(v, p))
    return pts


def projective_deletion(r, p, deleted=()):
    """Simple GF(p)-representable matroid PG(r-1, p) minus a set of projective points.

    Returns ``(lattice, points)`` where ``points[e]`` is the representative of ground
    element ``e``. Flats are the subspaces S with S = span(S minus deleted points).
    """
    _check_prime(p)
    all_points = projective_points(r, p)
    removed = {normalize(v, p) for v in deleted}
    if not removed <= set(all_points):
        raise ValueError("deleted vectors must lie in GF(p)^r")
    points = [v for v in all_points if v not in removed]
    index = {v: e for e, v in enumerate(points)}
    if _rank_mod_p(points, p) != r:
        raise ValueError("the remaining points do not span GF(p)^r")
    flats = {}
    for basis in _rref_subspaces(r, p):
        d = len(basis)
        kept = [v for v in (_span_points(basis, p) if d else ()) if v in index]
        if (_rank_mod_p(kept, p) if kept else 0) != d:
            continue
        mask = sum(_bit(index[v]) for v in kept)
        flats[mask] = d
    order = sorted(flats, key=lambda f: (flats[f], f))
    return FlatLattice(len(points), tuple(order), tuple(flats[f] for f in order)), points


# ---------------------------------------------------------------- operations


def direct_sum(a, b):
    shift = a.size
    flats = {}
    for fa, ra in zip(a.flats, a.ranks):
        for fb, rb in zip(b.flats, b.ranks):
            flats[fa | (fb << shift)] = ra + rb
    order = sorted(flats, key=lambda f: (flats[f], f))
    return FlatLattice(a.size + b.size, tuple(order), tuple(flats[f] for f in order))


def truncation(lattice, k):
    """Rank-k truncation: the flats of rank < k together with the ground set (rank k)."""
    if not 0 <= k <= lattice.rank:
        raise ValueError("truncation rank out of range")
    keep = [(f, r) for f, r in zip(lattice.flats, lattice.ranks) if r < k]
    keep.append(((1 << lattice.size) - 1, k))
    return FlatLattice(lattice.size, tuple(f for f, _ in keep), tuple(r for _, r in keep))


# ---------------------------------------------------------------- interval characteristic polynomials


def upsets(lattice):
    """For each flat index i, the indices j >= i (in rank order) with flat_i subset of flat_j."""
    flats = lattice.flats
    out = []
    for i, f in enumerate(flats):
        out.append(tuple(j for j in range(i, len(flats)) if flats[j] & f == f))
    return out


def interval_characteristic(lattice):
    """Pure-Python reference: list over i of dicts j -> chi_[F_i, F_j] coefficient tuple."""
    flats, ranks = lattice.flats, lattice.ranks
    ups = upsets(lattice)
    out = []
    for i, up in enumerate(ups):
        mu = {}
        chis = {}
        for j in up:
            g = flats[j]
            below = [h for h in up if ranks[h] < ranks[j] and flats[h] & g == flats[h]]
            m = -sum(mu[h] for h in below) if j != i else 1
            mu[j] = m
            coeffs = [0] * (ranks[j] - ranks[i] + 1)
            for h in below:
                coeffs[ranks[j] - ranks[h]] += mu[h]
            coeffs[0] += m
            chis[j] = trim(coeffs)
        out.append(chis)
    return out
