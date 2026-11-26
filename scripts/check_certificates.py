"""Regenerate the stored finite mathematical certificates and compare exactly."""

import json
import subprocess
import sys

from scripts.check_catalogue import ROOT
from solved.seven_steps import catalogue


def canonical(data):
    return json.loads(json.dumps(data))


def main():
    cases = [
        ("verify_nonsquare_bound", "nonsquare-bound.json", []),
        ("verify_square_instability", "square-instability.json", ["--least", "--powers"]),
        ("chain_catalogue", "chains.json", []),
        ("classical", "classical.json", []),
        ("verify_order", "order-checks.json", []),
        ("verify_two_small", "two-small-classification.json", []),
        ("counting_check", "counting-level10.json", ["--level", "10"]),
        ("counting_check", "counting-level12.json", ["--level", "12"]),
    ]
    for module, name, args in cases:
        result = subprocess.run(
            [sys.executable, "-B", "-m", f"checks.{module}", *args],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
        current = json.loads(result.stdout)
        if module == "counting_check":
            del current["filtered_seconds"]
            del current["reference_seconds"]
        expected = json.loads((ROOT / "checks" / "expected" / name).read_text())
        if current != expected:
            raise ValueError(f"certificate mismatch: {name}")
        print(f"Matched {name}", flush=True)
    expected = json.loads((ROOT / "checks/expected/seven-steps.json").read_text())
    if canonical(catalogue()) != expected:
        raise ValueError("certificate mismatch: seven-steps.json")
    subprocess.run([sys.executable, "-B", "-m", "checks.verify_seven"], cwd=ROOT, check=True)
    subprocess.run([sys.executable, "-B", "-m", "checks.verify_chains"], cwd=ROOT, check=True)
    print(f"Matched all {len(cases) + 1} certificates and independent enumerations.")


if __name__ == "__main__":
    main()
