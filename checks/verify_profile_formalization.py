"""Kernel-check Python/Lean model agreement on an exhaustive small-control family.

The universal Lean theorems do not depend on these cases. These checks compare
the executable Python representation with the formally defined one, including
the conversion from absolute mark numbers to newest-first history addresses.
"""

import json
import subprocess
import tempfile
from itertools import product
from pathlib import Path

from checks.verify_control_cutoffs import controls
from solved.control_profiles import endpoint, ideal_intersection, profile
from solved.square_controls import Description

ROOT = Path(__file__).resolve().parents[1]


def lean_box(description, free):
    """Convert a validated test description into a box with the same anchor."""
    selected = set(free)
    rows = []
    lower = []
    upper = []
    run = 0
    for position, (op, a, b) in enumerate(description.control):
        # Python mark 0 is the original 1; Lean address 0 is the newest value.
        left = position - a
        if op == "squares":
            g = description.runs[run]
            if run in selected:
                rows.append(f".unbounded {left} {g}")
                lower.append(g)
                upper.append(None)
            else:
                rows.append(f".bounded {left} 1 {g}")
                lower.append(1)
                upper.append(g)
            run += 1
        else:
            rows.append(f".{'add' if op == '+' else 'mul'} {left} {position - b}")
    return "[" + ", ".join(rows) + "]", Description(description.control, tuple(lower)), tuple(upper)


def fixtures():
    for control in controls(3):
        runs = tuple(1 + i % 2 for i, row in enumerate(control) if row[0] == "squares")
        base = Description(control, runs)
        for mask in product((False, True), repeat=len(runs)):
            yield base, tuple(i for i, flag in enumerate(mask) if flag)
    # Nontrivial sharing, a constant recomputed after free runs, and multiple
    # incomparable minimal points lie beyond the exhaustive three-block range.
    extra = [
        Description((("+", 0, 0), ("squares", 1, None), ("squares", 1, None), ("*", 2, 3)), (1, 1)),
        Description(
            (
                ("+", 0, 0),
                ("+", 1, 0),
                ("squares", 1, None),
                ("+", 3, 0),
                ("squares", 1, None),
                ("+", 5, 0),
                ("*", 4, 6),
                ("*", 2, 7),
            ),
            (1, 1),
        ),
        Description(
            (("+", 0, 0), ("squares", 1, None), ("+", 0, 0), ("squares", 3, None), ("+", 2, 4)),
            (2, 1),
        ),
        Description((("+", 0, 0), ("+", 1, 0), ("squares", 2, None), ("+", 3, 3)), (1,)),
    ]
    for base in extra:
        for mask in product((False, True), repeat=len(base.runs)):
            yield base, tuple(i for i, flag in enumerate(mask) if flag)


def source():
    lines = [
        "import IdealOracle",
        "set_option maxRecDepth 10000",
        "set_option maxHeartbeats 1000000",
    ]
    count = decisions = 0
    for count, (base, free) in enumerate(fixtures(), 1):
        literal, lower, upper = lean_box(base, free)
        bound = profile(base, free)
        coefficients = [bound.coefficient(i) for i in range(len(free) + 1)]
        lines.append(f"def box{count} : List SolvedIdeal.Constraint := {literal}")
        lines.append(f"def code{count} := box{count}.map SolvedIdeal.anchor")
        lines.append(f"def state{count} := SolvedProfiles.build code{count} SolvedProfiles.initial")
        lines.append(
            f"example : SolvedIdeal.Nonempty box{count} := by simp [box{count}, SolvedIdeal.Nonempty]"
        )
        actual = [f"(state{count}.history 0).coefficient {i}" for i in range(len(free) + 1)]
        expected = "[" + ", ".join(map(str, coefficients)) + "]"
        lines.append(f"example : [{', '.join(actual)}] = {expected} := by decide")
        lines.append(f"example : state{count}.dimension = {len(free)} := by decide")
        for t in (0, 1):
            runs = tuple(g + t if i in free else g for i, g in enumerate(base.runs))
            value = endpoint(Description(base.control, runs))
            lines.append(
                f"example : SolvedProfiles.endpoint code{count} {t} = {value} := by decide"
            )
        for excess in range(min(3, lower.length) + 1):
            expected_hit = not ideal_intersection(lower, excess, upper).empty
            expected_bool = "true" if expected_hit else "false"
            lines.append(
                f"example : {excess} ≤ SolvedInflation.cost (SolvedIdeal.diagonal box{count} 0)"
                " := by decide"
            )
            lines.append(
                f"example : SolvedIdeal.decision box{count} {excess} = {expected_bool} := by decide"
            )
            decisions += 1
    return "\n".join(lines) + "\n", {
        "exhaustive_three_block_profiles": 765,
        "additional_shared_profiles": count - 765,
        "profile_cases": count,
        "endpoint_cases": 2 * count,
        "box_decisions": decisions,
    }


def verify():
    code, stats = source()
    with tempfile.TemporaryDirectory(prefix="solved-profile-models-") as directory:
        path = Path(directory) / "ProfileModels.lean"
        path.write_text(code)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True
        )
        if result.returncode:
            raise RuntimeError("Lean model comparison failed:\n" + result.stdout + result.stderr)
    return stats


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
