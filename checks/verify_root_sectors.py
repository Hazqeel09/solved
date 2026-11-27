"""Exhaustive finite checks of the supported square-root constructions."""

import argparse
import hashlib
import json
from collections import Counter
from itertools import combinations_with_replacement
from math import isqrt

from solved.chains import Chain, chains, level
from solved.root_sectors import reduce_square


def replay(chain):
    values = [1]
    for op, a, b in chain.recipes:
        if op not in ("+", "*") or not 0 <= a < len(values) or not 0 <= b < len(values):
            raise ArithmeticError("root certificate has an invalid operand")
        value = values[a] + values[b] if op == "+" else values[a] * values[b]
        if value <= values[-1]:
            raise ArithmeticError("root certificate does not increase")
        values.append(value)
    if tuple(values) != chain.values:
        raise ArithmeticError("root certificate replay disagrees")
    return values[-1]


def eligible(chain, defect):
    events = [i for i in range(1, len(chain.values)) if chain.values[i] != chain.values[i - 1] ** 2]
    word = "".join(
        "S" if level(chain.values[i]) == level(chain.values[i - 1]) else "G" for i in events[2:]
    )
    return (
        defect == 2
        and (
            len(events) in (3, 4, 7)
            or word in ("GGS", "GGSG", "GSG")
            or all(v & (v - 1) == 0 for v in chain.values)
        )
        and isqrt(chain.values[-1]) ** 2 == chain.values[-1]
    )


def verify(max_level=12, *, aliases=False):
    if type(max_level) is not int or not 2 <= max_level <= 12:
        raise ValueError("finite checker supports complete levels two through twelve")
    counts, savings, sectors = Counter(), Counter(), Counter()
    square_roots = set()
    digest = hashlib.sha256()
    alternatives = 0
    for defect, chain in chains((1 << (1 << max_level)) - 1, 2):
        if not eligible(chain, defect):
            continue
        candidates = [chain]
        if aliases:
            candidates = []
            prefix = chain.values[:-1]
            target = chain.values[-1]
            for a, b in combinations_with_replacement(range(len(prefix)), 2):
                for op, value in (("+", prefix[a] + prefix[b]), ("*", prefix[a] * prefix[b])):
                    if value == target:
                        for x, y in ((a, b), (b, a)) if a != b else ((a, b),):
                            candidates.append(
                                Chain(chain.values, (*chain.recipes[:-1], (op, x, y)))
                            )
            alternatives += len(candidates)
        for candidate in candidates:
            reduction = reduce_square(candidate)
            root = replay(reduction.chain)
            if root * root != chain.values[-1] or reduction.saved_instructions < 1:
                raise ArithmeticError("root certificate does not establish the promised saving")
            if len(reduction.chain.recipes) - level(root) > 2:
                raise ArithmeticError("reconstructed root leaves the defect class")
            counts[reduction.rule] += 1
            sectors[sum(y != x * x for x, y in zip(chain.values, chain.values[1:]))] += 1
            savings[reduction.saved_instructions] += 1
            square_roots.add(root)
            # Binary integer serialization remains valid above decimal-string limits.
            for row in (candidate.values, reduction.chain.values):
                digest.update(len(row).to_bytes(4, "big"))
                for value in row:
                    data = value.to_bytes((value.bit_length() + 7) // 8, "big")
                    digest.update(len(data).to_bytes(4, "big"))
                    digest.update(data)
            digest.update(reduction.rule.encode("ascii") + b"\0")
    return {
        "complete_through_level": max_level,
        "source_sector": "exactly two small steps; three, four or seven nonsquares, GGS/GGSG/GSG, or power-only histories",
        "checked_square_chains_or_recipe_variants": sum(counts.values()),
        "unique_roots": len(square_roots),
        "rules": dict(sorted(counts.items())),
        "canonical_nonsquares": {str(k): sectors[k] for k in sorted(sectors)},
        "saved_writes": {str(k): savings[k] for k in sorted(savings)},
        "all_final_recipe_variants": alternatives if aliases else None,
        "source_and_root_values_sha256": digest.hexdigest(),
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--level", type=int, default=12)
    parser.add_argument("--aliases", action="store_true")
    args = parser.parse_args()
    print(json.dumps(verify(args.level, aliases=args.aliases), indent=2))
