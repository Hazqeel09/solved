"""Exact assignments for one connected component of coupled arithmetic observations.

The path and operation primitives are shared within this package.
"""

from collections import defaultdict, deque
from dataclasses import dataclass
from typing import Optional

from .arithmetic import DomainError, calculate
from .rational import (
    IDENTITY,
    compose,
    fixed_points,
    image,
    relation,
    trace,
)

Path = tuple[tuple[str, int, bool], ...]


@dataclass(frozen=True)
class Edge:
    left: int
    right: int
    op: str
    target: int
    left_path: Path = ()
    right_path: Path = ()


@dataclass(frozen=True)
class Menu:
    # Root is the smallest vertex ID. One tuple gives all vertex values in sorted ID order.
    vertices: tuple[int, ...]
    assignments: tuple[tuple[int, ...], ...]
    constrained_by_cycle: bool
    # False means the balanced component needs a caller-supplied domain.
    enumerated: bool


def inverse(matrix):
    a, b, c, d = matrix
    return (d, -b, -c, a)


def _component(edges, constants, limit):
    if type(limit) is not int or limit < 1 or not edges:
        raise ValueError("need a positive cap and at least one constraint")

    def bounded(v):
        return type(v) is int and 1 <= v <= limit

    known = set()
    for k in constants:
        if not bounded(k):
            raise ValueError("invalid available constant")
        known.add(k)
    adjacency = defaultdict(list)
    relations = []
    for e in edges:
        if any(type(i) is not int or i < 0 for i in (e.left, e.right)):
            raise ValueError("invalid vertex")
        if e.op not in ("+", "-", "*", "/") or not bounded(e.target):
            raise ValueError("invalid terminal operation or output")
        for path in (e.left_path, e.right_path):
            for op, k, rev in path:
                if (
                    op not in ("+", "-", "*", "/")
                    or not bounded(k)
                    or k not in known
                    or type(rev) is not bool
                ):
                    raise ValueError("invalid path operation or unavailable constant")
        matrix = relation(e.left_path, e.right_path, e.op, e.target, False)
        adjacency[e.left].append((e.right, matrix))
        adjacency[e.right].append((e.left, inverse(matrix)))
        relations.append(matrix)
    vertices = tuple(sorted(adjacency))
    root = vertices[0]
    transforms = {root: IDENTITY}
    queue = deque([root])
    while queue:
        i = queue.popleft()
        for j, matrix in adjacency[i]:
            if j not in transforms:
                transforms[j] = compose(matrix, transforms[i])
                queue.append(j)
    if len(transforms) != len(vertices):
        raise ValueError("solve connected components separately")
    loops = []
    for e, matrix in zip(edges, relations):
        loop = compose(inverse(transforms[e.right]), compose(matrix, transforms[e.left]))
        if loop != IDENTITY:
            loops.append(loop)
    return vertices, transforms, loops


def solve(
    edges: tuple[Edge, ...],
    constants,
    limit: int,
    *,
    root_domain: Optional[set[int]] = None,
) -> Menu:
    """Unbalanced components are complete globally. Balanced ones can use a finite root domain."""
    vertices, transforms, loops = _component(edges, constants, limit)
    roots = None
    if root_domain is not None:
        roots = set()
        for v in root_domain:
            if type(v) is not int or not 1 <= v <= limit:
                raise ValueError("invalid root domain")
            roots.add(v)
    informative = bool(loops)
    for loop in loops:
        possible = set(fixed_points(loop, limit))
        roots = possible if roots is None else roots & possible
    if roots is None:
        return Menu(vertices, (), informative, False)
    assignments = []
    for h in sorted(roots):
        values = {i: image(transform, h, limit) for i, transform in transforms.items()}
        if None in values.values():
            continue
        # Clearing denominators does not preserve legal execution at every intermediate.
        try:
            for edge in edges:
                left, _ = trace(values[edge.left], edge.left_path, limit)
                right, _ = trace(values[edge.right], edge.right_path, limit)
                if calculate(edge.op, left, right, limit) != edge.target:
                    break
            else:
                assignments.append(tuple(values[i] for i in vertices))
        except DomainError:
            continue
    return Menu(vertices, tuple(assignments), informative, True)
