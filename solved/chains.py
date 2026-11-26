"""Enumerate monotone addition–multiplication chains with a bounded small-step defect."""

from dataclasses import dataclass
from itertools import combinations_with_replacement


def level(n: int) -> int:
    if type(n) is not int or n < 1:
        raise ValueError("expected a positive integer")
    return (n.bit_length() - 1).bit_length()


@dataclass(frozen=True)
class Chain:
    values: tuple[int, ...]
    # Each row references two earlier entries by zero-based index.
    recipes: tuple[tuple[str, int, int], ...]


def chains(limit: int, max_small: int = 2):
    """Visit every distinct value sequence once, retaining one recipe per step."""
    level(limit)
    if type(max_small) is not int or max_small < 0:
        raise ValueError("invalid small-step budget")

    def visit(values, recipes, defect):
        yield defect, Chain(values, recipes)
        last = values[-1]
        # A step staying at this level would spend one more small step.
        floor = last + 1
        if defect == max_small:
            floor = 1 << (1 << level(last))
        choices = {}
        for i, j in combinations_with_replacement(range(len(values)), 2):
            a, b = values[i], values[j]
            for v, op in ((a + b, "+"), (a * b, "*")):
                if floor <= v <= limit:
                    choices.setdefault(v, (op, i, j))
        for v, rule in sorted(choices.items()):
            yield from visit(
                values + (v,), recipes + (rule,), defect + int(level(v) == level(last))
            )

    yield from visit((1,), (), 0)


def catalogue(limit: int, max_small: int = 2):
    """Return shortest witnessed chains, per-defect endpoints and path counts."""
    best = {}
    endpoints = (
        [set() for _ in range(max_small + 1)] if type(max_small) is int and max_small >= 0 else []
    )
    counts = [0] * len(endpoints)
    for d, chain in chains(limit, max_small):
        n = chain.values[-1]
        endpoints[d].add(n)
        counts[d] += 1
        if n not in best or len(chain.values) < len(best[n].values):
            best[n] = chain
    return best, endpoints, counts
