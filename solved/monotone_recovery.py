"""Directed exact recovery from monotone polynomial interval observations.

All variables have positive integer interval domains. Polynomials have
nonnegative integer coefficients and binary-encoded nonnegative exponents.
Only certified functional directions are used; uncovered variables remain
undetermined. See results/directed-monotone-recovery/PROOF.md.
"""

from collections import deque
from dataclasses import dataclass

from sympy.utilities.iterables import strongly_connected_components


def _pow_cap(base, exponent, cap):
    result = 1
    base = min(base, cap)
    while exponent:
        if exponent & 1:
            result = min(cap, result * base)
        exponent >>= 1
        if exponent:
            base = min(cap, base * base)
    return min(result, cap)


def _power_gap(base, exponent, cap):
    """min(cap, (base+1)**exponent - base**exponent), without capped subtraction."""
    lo = hi = 1
    gap = 0
    for bit in bin(exponent)[2:]:
        gap = min(cap, gap * (lo + hi))
        lo, hi = min(cap, lo * lo), min(cap, hi * hi)
        if bit == "1":
            gap = min(cap, (base + 1) * gap + lo)
            lo, hi = min(cap, base * lo), min(cap, (base + 1) * hi)
    return gap


@dataclass(frozen=True)
class Polynomial:
    # (coefficient, exponent of left input, exponent of right input)
    terms: tuple[tuple[int, int, int], ...]

    def __post_init__(self):
        merged = {}
        for row in self.terms:
            row = tuple(row)
            if len(row) != 3 or any(type(v) is not int or v < 0 for v in row):
                raise ValueError("nonnegative integer polynomial terms required")
            c, p, q = row
            if c:
                merged[p, q] = merged.get((p, q), 0) + c
        object.__setattr__(self, "terms", tuple((c, p, q) for (p, q), c in sorted(merged.items())))

    def evaluate(self, x, y, cap):
        """Return min(F(x,y), cap); every intermediate has bounded bit length."""
        if any(type(v) is not int or v < 1 for v in (x, y, cap)):
            raise ValueError("positive integer inputs and cap required")
        result = 0
        for c, p, q in self.terms:
            term = min(c, cap) * _pow_cap(x, p, cap)
            term = min(cap, term) * _pow_cap(y, q, cap)
            result = min(cap, result + min(cap, term))
            if result == cap:
                break
        return result

    def increments(self, x, y, cap):
        """Capped exact coordinate increments at the lower corner of a domain."""
        if any(type(v) is not int or v < 1 for v in (x, y, cap)):
            raise ValueError("positive integer inputs and cap required")
        dx = dy = 0
        for c, p, q in self.terms:
            # Positive-product formulas preserve truncation; subtracting two
            # independently truncated powers would not preserve their difference.
            dx = min(cap, dx + min(cap, min(c, cap) * _power_gap(x, p, cap)) * _pow_cap(y, q, cap))
            dy = min(cap, dy + min(cap, min(c, cap) * _power_gap(y, q, cap)) * _pow_cap(x, p, cap))
        return dx, dy


@dataclass(frozen=True)
class Observation:
    left: int
    right: int
    polynomial: Polynomial
    lower: int
    upper: int


@dataclass(frozen=True)
class Arc:
    source: int
    destination: int
    edge: int
    source_is_left: bool


@dataclass(frozen=True)
class MonotoneRecovery:
    status: str
    values: tuple[int, ...] | None
    forced: tuple[tuple[int, int], ...]
    arcs: tuple[Arc, ...]
    walks: tuple[tuple[int, tuple[int, ...]], ...]
    evaluations: int  # Full polynomial or affine coefficient evaluations; excludes gap setup.


def _last_below(low, high, upper, evaluate):
    """Largest admissible integer, clamped to low when the feasible set is empty."""
    while low < high:
        middle = (low + high + 1) // 2
        if evaluate(middle) <= upper:
            low = middle
        else:
            high = middle - 1
    return low


def _odd_walk(root, vertices, adjacent, arcs):
    """An odd directed closed walk, obtained from the two parity copies of an SCC."""
    start, finish = (root, 0), (root, 1)
    parent = {start: None}
    queue = deque([start])
    while queue and finish not in parent:
        u, parity = queue.popleft()
        for index in adjacent[u]:
            arc = arcs[index]
            state = (arc.destination, 1 - parity)
            if arc.destination in vertices and state not in parent:
                parent[state] = ((u, parity), index)
                queue.append(state)
    if finish not in parent:
        return None
    walk = []
    cursor = finish
    while cursor != start:
        cursor, index = parent[cursor]
        walk.append(index)
    return tuple(reversed(walk))


def recover(domains, observations):
    """Recover a unique tuple when functional directed paths cover every variable.

    Returns undetermined outside the anchor/constant-map/odd-cycle coverage
    condition, unless a separately sound contradiction has been found.
    """
    domains = tuple(tuple(row) for row in domains)
    if not domains or any(
        len(row) != 2 or any(type(v) is not int for v in row) or not 1 <= row[0] <= row[1]
        for row in domains
    ):
        raise ValueError("nonempty positive integer domains required")
    observations = tuple(observations)
    size = len(domains)
    for row in observations:
        if not isinstance(row, Observation) or not isinstance(row.polynomial, Polynomial):
            raise ValueError("polynomial observations required")
        if any(type(v) is not int for v in (row.left, row.right, row.lower, row.upper)) or not (
            0 <= row.left < size and 0 <= row.right < size and 0 <= row.lower <= row.upper
        ):
            raise ValueError("invalid observation endpoints or bounds")
    arcs = []
    diagonal_seeds = []
    adjacent = [[] for _ in domains]
    values = [None] * size
    walks = []
    evaluations = 0

    def result(status):
        return MonotoneRecovery(
            status,
            tuple(values) if status == "unique" else None,
            tuple((i, v) for i, v in enumerate(values) if v is not None),
            tuple(arcs),
            tuple(walks),
            evaluations,
        )

    def evaluate(index, x, y):
        nonlocal evaluations
        evaluations += 1
        edge = observations[index]
        return edge.polynomial.evaluate(x, y, edge.upper + 1)

    for index, row in enumerate(observations):
        u, v = row.left, row.right
        if (
            evaluate(index, domains[u][0], domains[v][0]) > row.upper
            or evaluate(index, domains[u][1], domains[v][1]) < row.lower
        ):
            return result("infeasible")
        width = row.upper - row.lower
        if u == v:
            diagonal = Polynomial(tuple((c, p + q, 0) for c, p, q in row.polynomial.terms))
            if diagonal.increments(domains[u][0], 1, width + 1)[0] > width:
                diagonal_seeds.append(index)
        dx, dy = row.polynomial.increments(domains[u][0], domains[v][0], width + 1)
        for source, destination, forward, gap in ((u, v, True, dy), (v, u, False, dx)):
            if gap > width:
                adjacent[source].append(len(arcs))
                arcs.append(Arc(source, destination, index, forward))

    transported = {}
    affine = [
        all(
            term[2 if arc.source_is_left else 1] <= 1
            for term in observations[arc.edge].polynomial.terms
        )
        for arc in arcs
    ]

    def transport(index, value):
        nonlocal evaluations
        key = (index, value)
        if key not in transported:
            arc = arcs[index]
            edge = observations[arc.edge]
            low, high = domains[arc.destination]
            if affine[index]:
                # F(source, destination) = slope*destination + offset.
                # The existing quotient transport is this exact special case.
                evaluations += 1
                slope = offset = 0
                cap = edge.upper + 1
                for coefficient, p, q in edge.polynomial.terms:
                    source_power, destination_power = (p, q) if arc.source_is_left else (q, p)
                    term = min(cap, min(coefficient, cap) * _pow_cap(value, source_power, cap))
                    if destination_power:
                        slope = min(cap, slope + term)
                    else:
                        offset = min(cap, offset + term)
                if not slope:
                    raise ArithmeticError("a certified affine direction must have positive slope")
                if slope > edge.upper or offset > edge.upper:
                    transported[key] = low
                else:
                    transported[key] = min(high, max(low, (edge.upper - offset) // slope))
                return transported[key]

            def at(candidate):
                x, y = (value, candidate) if arc.source_is_left else (candidate, value)
                return evaluate(arc.edge, x, y)

            transported[key] = _last_below(low, high, edge.upper, at)
        return transported[key]

    queue = deque()

    def assign(vertex, value):
        if values[vertex] is not None:
            return values[vertex] == value
        values[vertex] = value
        queue.append(vertex)
        return True

    def propagate():
        while queue:
            u = queue.popleft()
            for index in adjacent[u]:
                arc = arcs[index]
                value = transport(index, values[u])
                x, y = (values[u], value) if arc.source_is_left else (value, values[u])
                edge = observations[arc.edge]
                if not edge.lower <= evaluate(arc.edge, x, y) <= edge.upper:
                    return False
                if not assign(arc.destination, value):
                    return False
        return True

    for vertex, (low, high) in enumerate(domains):
        if low == high:
            assign(vertex, low)
    # A self-observation uses the same value in both positions. Its diagonal
    # gap may be large enough even when neither separate-coordinate gap is.
    for index in diagonal_seeds:
        edge = observations[index]
        low, high = domains[edge.left]
        value = _last_below(low, high, edge.upper, lambda v: evaluate(index, v, v))
        if not edge.lower <= evaluate(index, value, value) <= edge.upper or not assign(
            edge.left, value
        ):
            return result("infeasible")
    # A functional observation independent of its source fixes the destination.
    for index, arc in enumerate(arcs):
        terms = observations[arc.edge].polynomial.terms
        source_power = 1 if arc.source_is_left else 2
        if all(term[source_power] == 0 for term in terms):
            source = domains[arc.source][0]
            value = transport(index, source)
            x, y = (source, value) if arc.source_is_left else (value, source)
            edge = observations[arc.edge]
            if not edge.lower <= evaluate(arc.edge, x, y) <= edge.upper or not assign(
                arc.destination, value
            ):
                return result("infeasible")
    if not propagate():
        return result("infeasible")

    components = strongly_connected_components(
        (list(range(size)), [(arc.source, arc.destination) for arc in arcs])
    )
    for component in components:
        root = min(component)
        if values[root] is not None:
            continue
        walk = _odd_walk(root, set(component), adjacent, arcs)
        if walk is None:
            continue
        walks.append((root, walk))

        def returned(value):
            for index in walk:
                value = transport(index, value)
            return value

        low, high = domains[root]
        while low < high:
            middle = (low + high + 1) // 2
            if returned(middle) >= middle:
                low = middle
            else:
                high = middle - 1
        if returned(low) != low or not assign(root, low) or not propagate():
            return result("infeasible")
    # This also checks constraints with no functional direction, and constants
    # inferred through an observation whose source was never assigned.
    for index, row in enumerate(observations):
        u, v = row.left, row.right
        if values[u] is not None and values[v] is not None:
            if not row.lower <= evaluate(index, values[u], values[v]) <= row.upper:
                return result("infeasible")
    return result("unique" if all(value is not None for value in values) else "undetermined")
