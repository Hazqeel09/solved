"""Exact product-interval feasibility over explicitly supplied factor palettes."""

from bisect import bisect_left, bisect_right
from dataclasses import dataclass

from sympy.utilities.iterables import strongly_connected_components


@dataclass(frozen=True)
class PaletteSolution:
    values: tuple[int, ...] | None
    variables: int
    clauses: int


def _prepare(palettes, edges):
    raw = [tuple(row) for row in palettes]
    if any(type(v) is not int or v < 1 for row in raw for v in row):
        raise ValueError("palettes require positive integers")
    domains = [tuple(sorted(set(row))) for row in raw]
    edges = tuple(tuple(row) for row in edges)
    n = len(domains)
    for edge in edges:
        if len(edge) != 4 or any(type(v) is not int for v in edge):
            raise ValueError("invalid product edge")
        u, v, low, high = edge
        if not (0 <= u < n and 0 <= v < n and 1 <= low <= high):
            raise ValueError("invalid product bounds or endpoints")
    return domains, edges


def solve(palettes, edges):
    domains, edges = _prepare(palettes, edges)
    if any(not row for row in domains):
        return PaletteSolution(None, 0, 0)
    # Variable zero is forced true, providing both boundary literals.
    count = 1
    offsets = []
    for row in domains:
        offsets.append(count)
        count += len(row) - 1
    implications = []
    clauses = 0

    def literal(i, threshold):
        if threshold <= 0:
            return 0
        if threshold >= len(domains[i]):
            return 1
        return 2 * (offsets[i] + threshold - 1)

    def clause(a, b):
        nonlocal clauses
        clauses += 1
        implications.extend(((a ^ 1, b), (b ^ 1, a)))

    clause(0, 0)
    for i, row in enumerate(domains):
        for k in range(1, len(row) - 1):
            clause(literal(i, k + 1) ^ 1, literal(i, k))
    for u, v, lower, upper in edges:
        if len(domains[u]) > len(domains[v]):
            u, v = v, u
        for k, a in enumerate(domains[u]):
            # x >= a implies y <= floor(upper/a).
            first_excluded = bisect_right(domains[v], upper // a)
            clause(literal(u, k) ^ 1, literal(v, first_excluded) ^ 1)
            # x <= a implies y >= ceil(lower/a).
            first_allowed = bisect_left(domains[v], (lower + a - 1) // a)
            clause(literal(u, k + 1), literal(v, first_allowed))
    parts = strongly_connected_components((list(range(2 * count)), implications))
    component = {v: i for i, part in enumerate(parts) for v in part}
    if any(component[2 * i] == component[2 * i + 1] for i in range(count)):
        return PaletteSolution(None, count, clauses)
    truth = {2 * i: component[2 * i] < component[2 * i + 1] for i in range(count)}
    values = []
    for i, row in enumerate(domains):
        selected = 0
        for k in range(1, len(row)):
            if truth[literal(i, k)]:
                selected = k
        values.append(row[selected])
    if any(not low <= values[u] * values[v] <= high for u, v, low, high in edges):
        raise ArithmeticError("decoded threshold assignment violates a product interval")
    return PaletteSolution(tuple(values), count, clauses)


def bottleneck(palettes, costs, edges):
    """Minimize the largest supplied unary construction cost, keeping all ties feasible."""
    palettes = tuple(tuple(row) for row in palettes)
    costs = tuple(tuple(row) for row in costs)
    if len(costs) != len(palettes) or any(len(a) != len(b) for a, b in zip(palettes, costs)):
        raise ValueError("one cost per palette occurrence is required")
    if any(type(c) is not int or c < 0 for row in costs for c in row):
        raise ValueError("costs must be nonnegative integers")
    edges = tuple(edges)
    unconstrained = solve(palettes, edges)
    if unconstrained.values is None:
        return None, unconstrained
    levels = sorted({c for row in costs for c in row})
    if not levels:
        return 0, unconstrained
    low, high = 0, len(levels) - 1
    while low < high:
        mid = (low + high) // 2
        restricted = [
            tuple(v for v, c in zip(row, cs) if c <= levels[mid])
            for row, cs in zip(palettes, costs)
        ]
        tested = solve(restricted, edges)
        if tested.values is None:
            low = mid + 1
        else:
            high = mid
    restricted = [
        tuple(v for v, c in zip(row, cs) if c <= levels[low]) for row, cs in zip(palettes, costs)
    ]
    best = solve(restricted, edges)
    return levels[low], best


def narrow_solutions(palettes, edges):
    """Enumerate every tuple in a connected narrow-error component in polynomial time."""
    domains, edges = _prepare(palettes, edges)
    if any(not row for row in domains):
        return
    if not domains:
        yield ()
        return
    adjacent = [[] for _ in domains]
    for i, (u, v, low, high) in enumerate(edges):
        if high - low >= min(domains[u][0], domains[v][0]):
            raise ValueError("interval width exceeds the narrow-error guarantee")
        adjacent[u].append((v, i))
        adjacent[v].append((u, i))
    root = min(range(len(domains)), key=lambda i: len(domains[i]))
    parents = {root: None}
    order = [root]
    for u in order:
        for v, edge in adjacent[u]:
            if v not in parents:
                parents[v] = (u, edge)
                order.append(v)
    if len(order) != len(domains):
        raise ValueError("enumerate connected components separately")
    allowed = [set(row) for row in domains]
    for start in domains[root]:
        values = [0] * len(domains)
        values[root] = start
        for v in order[1:]:
            u, edge = parents[v]
            lower, upper = edges[edge][2:]
            value = upper // values[u]
            if value not in allowed[v] or value * values[u] < lower:
                break
            values[v] = value
        else:
            if all(lower <= values[u] * values[v] <= upper for u, v, lower, upper in edges):
                yield tuple(values)


def min_cost_narrow(palettes, costs, edges):
    """Minimize a sum of supplied unary costs within a connected narrow-error instance."""
    palettes = tuple(tuple(row) for row in palettes)
    costs = tuple(tuple(row) for row in costs)
    if len(costs) != len(palettes) or any(len(a) != len(b) for a, b in zip(palettes, costs)):
        raise ValueError("one cost per palette occurrence is required")
    if any(type(c) is not int or c < 0 for row in costs for c in row):
        raise ValueError("costs must be nonnegative integers")
    prices = []
    for row, cs in zip(palettes, costs):
        price = {}
        for value, cost in zip(row, cs):
            price[value] = min(price.get(value, cost), cost)
        prices.append(price)
    best = None
    best_cost = None
    for values in narrow_solutions(palettes, edges):
        cost = sum(price[value] for price, value in zip(prices, values))
        if best_cost is None or cost < best_cost:
            best, best_cost = values, cost
    return best_cost, best
