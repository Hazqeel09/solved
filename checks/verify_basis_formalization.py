"""Compare the proved Lean basis algorithm with the optimized Python search.

Universal correctness is established by the Lean theorems. Here the compiled
Lean function runs on finite fixtures; unlike the profile checker, this is
an executable conformance test, not a collection of kernel-evaluated examples.
"""

import json
import subprocess
import tempfile
from pathlib import Path

from checks.verify_control_cutoffs import controls
from solved.control_basis import admissible_bases, minimal_basis
from solved.square_controls import Description

ROOT = Path(__file__).resolve().parents[1]


def fixtures():
    for control in controls(3):
        for excess in range(4):
            _, bases = admissible_bases(control, excess)
            for base in bases:
                yield base, excess, None
    parallel = Description(
        (("+", 0, 0), ("squares", 1, None), ("squares", 1, None), ("*", 2, 3)), (1, 1)
    )
    fermat = Description(
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
    )
    for base, excess in ((parallel, 3), (fermat, 6)):
        for upper in (None, (1, 1), (1, None), (None, 1), (2, 3), (3, 2), (2, 2)):
            yield base, excess, upper
    yield Description(parallel.control, (2, 2)), 3, None
    yield Description(fermat.control, (1, 2)), 6, (3, None)


def source():
    lines = [
        "import ArithmeticBasis",
        "open SolvedBasis SolvedArithmeticBasis",
        "set_option maxRecDepth 10000",
        "set_option maxHeartbeats 1000000",
    ]
    expected = []
    for number, (base, excess, upper) in enumerate(fixtures()):
        d = len(base.control)
        cells, bounds = [], []
        run = 0
        for i, (op, a, b) in enumerate(base.control):
            if op == "squares":
                g = base.runs[run]
                cells.append(f"Cell.squares {i - a} {g}")
                limit = None if upper is None else upper[run]
                bounds.append("none" if limit is None else f"some {limit - g}")
                run += 1
            else:
                cells.append(f"Cell.{'add' if op == '+' else 'mul'} {i - a} {i - b}")
                bounds.append("none")
        literal = "[" + ",".join(cells) + "]"
        box = "[" + ",".join(bounds) + "]"
        lines.append(f"def template{number} : Template {d} := fun i => ({literal}).get i")
        lines.append(f"def box{number} : Box {d} := fun i => ({box}).get i")
        lines.append(f"theorem valid{number} : Valid template{number} := by decide")
        lines.append(
            f"theorem index{number} : {excess} ≤ SolvedInflation.cost "
            f"(emit {d} template{number} (fun _ => 0)) := by decide"
        )
        lines.append(
            f"#eval let rows := basis (oracle template{number} {excess} valid{number} index{number}) "
            f"box{number}; [[upperIndex template{number} {excess} rows]] ++ "
            f"rows.map (fun p => (indices {d}).map p)"
        )
        result = minimal_basis(base, excess, upper)
        if result.status != "complete":
            raise ArithmeticError("Python basis comparison did not complete")
        rows = []
        for point in result.minimals:
            full = []
            run = 0
            for op, _, _ in base.control:
                if op == "squares":
                    full.append(point[run] - base.runs[run])
                    run += 1
                else:
                    full.append(0)
            rows.append(full)
        expected.append([[result.cutoff], *sorted(rows)])
    return "\n".join(lines) + "\n", expected


def decode(output):
    decoder = json.JSONDecoder()
    rows = []
    remaining = output.strip()
    while remaining:
        value, end = decoder.raw_decode(remaining)
        rows.append(value)
        remaining = remaining[end:].lstrip()
    return rows


def verify():
    code, expected = source()
    with tempfile.TemporaryDirectory(prefix="solved-basis-models-") as directory:
        path = Path(directory) / "BasisModels.lean"
        path.write_text(code)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True
        )
        if result.returncode:
            raise RuntimeError("Lean basis comparison failed:\n" + result.stdout + result.stderr)
        actual = decode(result.stdout)
    if len(actual) != len(expected):
        raise ArithmeticError("basis comparison omitted or added cases")
    for i, (actual_row, expected_row) in enumerate(zip(actual, expected)):
        if not actual_row or [actual_row[0], *sorted(actual_row[1:])] != expected_row:
            raise ArithmeticError(f"basis/cutoff disagreement at case {i}")
    return {
        "basis_cases": len(expected),
        "minimal_points": sum(len(row) - 1 for row in expected),
        "maximum_compared_cutoff": max(row[0][0] for row in expected),
        "mode": "compiled Lean execution compared with Python",
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
