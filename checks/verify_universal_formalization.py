"""Check clipping, guarded leaves and small finite aggregates of the universal construction.

This never evaluates the universal threshold. The aggregate fixtures use
independently chosen block/address bounds at most two, not the universal
12*C+13 bound. Their numbers are component checks, not universal thresholds.
"""

import json
import subprocess
import tempfile
from itertools import product
from pathlib import Path

from checks.verify_basis_formalization import decode
from checks.verify_control_cutoffs import controls
from solved.control_basis import minimal_basis
from solved.square_controls import Description

ROOT = Path(__file__).resolve().parents[1]
AGGREGATES = ((0, 0), (0, 1), (1, 1), (0, 2), (1, 2), (2, 2))


def cell_literal(cells):
    return "[" + ",".join(f"Cell.{op} {a} {b}" for op, a, b in cells) + "]"


def instruction_literal(code):
    return "[" + ",".join(f"SolvedMarked.Instr.{op} {a} {b}" for op, a, b in code) + "]"


def descriptions():
    for control in controls(3):
        dimension = sum(row[0] == "squares" for row in control)
        for runs in product((1, 2, 5), repeat=dimension):
            code, run = [], 0
            for i, (op, a, b) in enumerate(control):
                if op == "squares":
                    code.append(("sqRun", i - a, runs[run]))
                    run += 1
                else:
                    code.append(("add" if op == "+" else "mul", i - a, i - b))
            yield tuple(code)
    for count in (0, 10**100):
        yield (("sqRun", 0, count),)
        yield (("add", 0, 0), ("sqRun", 0, count), ("mul", 0, 1))


def alphabet(excess_bound, address_bound):
    for a in range(address_bound + 1):
        for b in range(address_bound + 1):
            yield "add", a, b
            yield "mul", a, b
        for base in range(1, excess_bound + 2):
            yield "squares", a, base


def python_leaf(cells, excess):
    control, runs = [], []
    for i, (op, a, b) in enumerate(cells):
        # The universal enumeration uses the formal extended history. An
        # out-of-range address is 1, represented by Python's initial mark.
        left = max(0, i - a)
        if op == "squares":
            if b < 1:
                return None
            control.append(("squares", left, None))
            runs.append(b)
        else:
            control.append(("+" if op == "add" else "*", left, max(0, i - b)))
    description = Description(tuple(control), tuple(runs))
    if description.length < excess:
        return None
    result = minimal_basis(description, excess)
    if result.status != "complete":
        raise ArithmeticError("small aggregate leaf did not complete")
    return result.cutoff


def reference_aggregate(excess_bound, bound):
    symbols = tuple(alphabet(excess_bound, bound))
    result = 0
    count = 0
    for size in range(bound + 1):
        for cells in product(symbols, repeat=size):
            count += 1
            for excess in range(excess_bound + 1):
                value = python_leaf(cells, excess)
                if value is not None:
                    result = max(result, value)
    return [count, result]


def source():
    lines = [
        "import UniversalCutoff",
        "open SolvedUniversal SolvedArithmeticBasis",
        "set_option maxRecDepth 10000",
    ]
    assertions = 0
    for code in descriptions():
        for bound in range(4):
            clipped = tuple(
                ("squares", a, min(k, bound + 1)) if op == "sqRun" else (op, a, k)
                for op, a, k in code
            )
            cost = sum(k if op == "squares" else 1 for op, _, k in clipped)
            expression = f"(clip {bound} {instruction_literal(code)})"
            lines.append(f"example : {expression} = {cell_literal(clipped)} := by rfl")
            lines.append(
                f"example : SolvedInflation.cost (baseProgram {expression}) = {cost} := by decide"
            )
            assertions += 2
    expected = []
    for excess, bound in AGGREGATES:
        lines.append(
            f"#eval [(boundedCells {excess} {bound}).length, "
            f"portfolio {excess} (boundedCells {excess} {bound})]"
        )
        expected.append(reference_aggregate(excess, bound))
    guards = [
        ((), 0),
        ((), 1),
        ((("squares", 0, 0),), 0),
        ((("add", 0, 0),), 0),
        ((("add", 0, 0),), 1),
        ((("add", 0, 0),), 2),
    ]
    for cells, excess in guards:
        value = python_leaf(cells, excess)
        lines.append(
            f"#eval match templateCutoff {cell_literal(cells)} {excess} with "
            "| none => ([] : List Nat) | some n => [n]"
        )
        expected.append([] if value is None else [value])
    return "\n".join(lines) + "\n", expected, assertions


def verify():
    code, expected, assertions = source()
    with tempfile.TemporaryDirectory(prefix="solved-universal-components-") as directory:
        path = Path(directory) / "UniversalComponents.lean"
        path.write_text(code)
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT, capture_output=True, text=True
        )
        if result.returncode:
            raise RuntimeError(
                "Universal component check failed:\n" + result.stdout + result.stderr
            )
        actual = decode(result.stdout)
    if actual != expected:
        raise ArithmeticError("universal-construction component outputs disagree")
    return {
        "kernel_clipping_and_cost_assertions": assertions,
        "small_portfolios": [
            {"excess_bound": e, "block_bound": m, "templates": row[0], "aggregate": row[1]}
            for (e, m), row in zip(AGGREGATES, expected)
        ],
        "guard_cases": len(expected) - len(AGGREGATES),
        "universal_threshold_evaluated": False,
    }


if __name__ == "__main__":
    print(json.dumps(verify(), indent=2))
