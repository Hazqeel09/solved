"""Exact recovery of positive integer factors from narrow product intervals."""

from collections import deque
from dataclasses import dataclass


@dataclass(frozen=True)
class Recovery:
    status: str
    values: tuple[int, ...] | None
    walk: tuple[tuple[int, int], ...]
    evaluations: int


def recover(domains, edges):
    """Solve a connected component with narrow edge intervals.

    Domains are inclusive (lower, upper) bounds. Edges are (u, v, lower,
    upper) product bounds, permitting loops and parallel observations. Every
    interval width must be smaller than both endpoint-domain lower bounds.
    An unanchored bipartite component returns undetermined.
    """
    domains = tuple(tuple(row) for row in domains)
    edges = tuple(tuple(row) for row in edges)
    n = len(domains)
    if not n or any(
        len(d) != 2 or any(type(x) is not int for x in d) or not 1 <= d[0] <= d[1] for d in domains
    ):
        raise ValueError("invalid positive integer domains")
    adjacent = [[] for _ in domains]
    for i, edge in enumerate(edges):
        if len(edge) != 4 or any(type(x) is not int for x in edge):
            raise ValueError("invalid product edge")
        u, v, lower, upper = edge
        if not (0 <= u < n and 0 <= v < n and 1 <= lower <= upper):
            raise ValueError("invalid product bounds or endpoints")
        if upper - lower >= min(domains[u][0], domains[v][0]):
            raise ValueError("product interval is too wide for unique-neighbor recovery")
        adjacent[u].append((v, i))
        adjacent[v].append((u, i))
    root = next((i for i, (low, high) in enumerate(domains) if low == high), 0)
    anchored = domains[root][0] == domains[root][1]
    parent = {root: None}
    depth = {root: 0}
    order = []
    queue = deque([root])
    conflict = None
    while queue:
        u = queue.popleft()
        order.append(u)
        for v, i in adjacent[u]:
            if v not in parent:
                parent[v] = (u, i)
                depth[v] = depth[u] + 1
                queue.append(v)
            elif depth[u] % 2 == depth[v] % 2 and conflict is None:
                conflict = (u, v, i)
    if len(order) != n:
        raise ValueError("a connected observation component is required")
    if not anchored and conflict is None:
        return Recovery("undetermined", None, (), 0)

    def transported(edge, destination, value):
        low, high = domains[destination]
        return min(high, max(low, edges[edge][3] // value))

    walk = []
    evaluations = 0
    if anchored:
        value = domains[root][0]
    else:
        u, v, edge = conflict
        forward = []
        while u != root:
            previous, i = parent[u]
            forward.append((i, u))
            u = previous
        walk = list(reversed(forward)) + [(edge, v)]
        while v != root:
            previous, i = parent[v]
            walk.append((i, previous))
            v = previous
        if len(walk) % 2 != 1:
            raise ArithmeticError("expected an odd closed walk")

        def returned(value):
            nonlocal evaluations
            evaluations += 1
            for edge, destination in walk:
                value = transported(edge, destination, value)
            return value

        low, high = domains[root]
        while low < high:
            middle = low + (high - low + 1) // 2
            if returned(middle) >= middle:
                low = middle
            else:
                high = middle - 1
        value = low
        if returned(value) != value:
            return Recovery("infeasible", None, tuple(walk), evaluations)
    values = [0] * n
    values[root] = value
    for v in order[1:]:
        u, edge = parent[v]
        values[v] = transported(edge, v, values[u])
    if any(not low <= values[u] * values[v] <= high for u, v, low, high in edges):
        return Recovery("infeasible", None, tuple(walk), evaluations)
    return Recovery("unique", tuple(values), tuple(walk), evaluations)
