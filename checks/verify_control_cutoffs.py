"""Exhaustive small-control census with independent finite parameter replay.

The symbolic engine covers all positive run lengths for the enumerated
controls. The replay checks are finite differential evidence, not a proof
of the engine's universal correctness or a cutoff for every AM program.
"""

import hashlib
import json
from itertools import combinations_with_replacement, product

from solved.control_basis import control_cutoff
from solved.square_controls import Description, expand


def controls(max_blocks):
    if type(max_blocks) is not int or max_blocks < 0:
        raise ValueError("nonnegative block bound required")

    def visit(prefix):
        yield prefix
        if len(prefix) == max_blocks:
            return
        addresses = range(len(prefix) + 1)
        for op in ("+", "*"):
            for a, b in combinations_with_replacement(addresses, 2):
                yield from visit((*prefix, (op, a, b)))
        for a in addresses:
            yield from visit((*prefix, ("squares", a, None)))

    yield from visit(())


def verify():
    rows = []
    histogram = {}
    finite_points = 0
    exact_points = 0
    basis_points = 0
    families = 0
    max_cutoff = 0
    for control in controls(3):
        histogram[len(control)] = histogram.get(len(control), 0) + 1
        for excess in range(4):
            result = control_cutoff(control, excess)
            if result.status != "complete" or result.cutoff is None:
                raise ArithmeticError("small-control census did not complete")
            families += 1
            max_cutoff = max(max_cutoff, result.cutoff)
            # Different admissible corners can have overlapping upward sets.
            # Keep each independently complete basis in its original domain.
            records = [(r.base.runs, r.minimals) for r in result.completed]
            basis_points += sum(len(points) for _, points in records)
            dimension = sum(row[0] == "squares" for row in control)
            for point in product(range(1, 5), repeat=dimension):
                description = Description(control, point)
                if description.length < excess:
                    continue
                index = description.length - excess
                endpoint = expand(description).values[-1]
                target = 2 ** (2**index) - 1
                finite_points += 1
                covered = any(
                    all(a <= b for a, b in zip(p, point)) for _, basis in records for p in basis
                )
                if covered != (endpoint <= target):
                    raise ArithmeticError("finite replay contradicts the computed upward basis")
                if endpoint == target:
                    exact_points += 1
                    if index >= result.cutoff:
                        raise ArithmeticError("exact solution lies beyond reported cutoff")
            rows.append([control, excess, result.cutoff, records])
    canonical = json.dumps(rows, separators=(",", ":")).encode("utf-8")
    return {
        "scope": "all legal controls of at most three blocks, commutative operands unordered",
        "blocks": 3,
        "excesses": [0, 1, 2, 3],
        "controls_by_blocks": {str(k): histogram[k] for k in sorted(histogram)},
        "completed_control_excess_families": families,
        "basis_points_counting_domain_overlaps": basis_points,
        "maximum_reported_template_cutoff": max_cutoff,
        "finite_replay_run_range": [1, 4],
        "finite_replay_points": finite_points,
        "finite_replay_exact_points": exact_points,
        "canonical_records_sha256": hashlib.sha256(canonical).hexdigest(),
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
