"""Write the generated Lean energy certificates, or check that they are up to date (--check).

Outputs formal/Formal/ICG/EvenFamilies.lean (certificates and graph-energy theorems),
formal/Formal/ICG/MultiFamilies.lean (region certificates for two symbolic primes),
formal/Formal/ICG/TwoPowThree.lean (cell certificates for 2^a * 3, solved/lean_two_pow_three.py),
formal/Formal/ICG/TwoPb/*.lean (step certificates for 2 p^b, solved/lean_two_pb.py, from
checks/expected/two-pb-certificates.json),
formal/FormalTests/Axioms.lean (axiom audit), docs/formalization-mathlib.json (theorem
registry of the Mathlib project) and the results table of
results/icg-energy-even-orders/PROOF.md, from checks/expected/icg-families.json.
"""

import argparse
import sys

from scripts.check_catalogue import ROOT
from solved.lean_icg import (
    axioms_from,
    multi_from,
    multi_table_from,
    registry_from,
    render_from,
    table_from,
)
from solved.lean_two_pb import HEADER as TWO_PB_HEADER
from solved.lean_two_pb import OUT as TWO_PB_DIR
from solved.lean_two_pb import render_all as two_pb_all
from solved.lean_two_pow_three import render_from as two_pow_three_from

SOURCE = ROOT / "checks" / "expected" / "icg-families.json"
MANUSCRIPT = ROOT / "results" / "icg-energy-even-orders" / "PROOF.md"
MULTI_MANUSCRIPT = ROOT / "results" / "icg-energy-two-symbolic-primes" / "PROOF.md"
TARGETS = {
    ROOT / "formal" / "Formal" / "ICG" / "EvenFamilies.lean": render_from,
    ROOT / "formal" / "Formal" / "ICG" / "MultiFamilies.lean": multi_from,
    ROOT / "formal" / "Formal" / "ICG" / "TwoPowThree.lean": two_pow_three_from,
    ROOT / "formal" / "FormalTests" / "Axioms.lean": axioms_from,
    ROOT / "docs" / "formalization-mathlib.json": registry_from,
    MANUSCRIPT: lambda source: table_from(source, MANUSCRIPT),
    MULTI_MANUSCRIPT: lambda source: multi_table_from(source, MULTI_MANUSCRIPT),
}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="fail if a file is out of date")
    args = parser.parse_args()
    stale = []
    for target, render in TARGETS.items():
        text = render(SOURCE)
        name = target.relative_to(ROOT)
        if args.check:
            if not target.exists() or target.read_text() != text:
                stale.append(str(name))
            continue
        target.write_text(text)
        print(f"Wrote {name}.")
    # formal/Formal/ICG/TwoPb/: the generated 2p^b step certificates (solved/lean_two_pb.py, from
    # checks/expected/two-pb-certificates.json). A generated file that is no longer produced is stale.
    two_pb = two_pb_all()
    for target, text in two_pb.items():
        name = target.relative_to(ROOT)
        if args.check:
            if not target.exists() or target.read_text() != text:
                stale.append(str(name))
            continue
        target.write_text(text)
        print(f"Wrote {name}.")
    for path in sorted(TWO_PB_DIR.glob("*.lean")):
        if path not in two_pb and path.read_text().startswith(TWO_PB_HEADER):
            if args.check:
                stale.append(f"{path.relative_to(ROOT)} (no longer generated)")
            else:
                path.unlink()
                print(f"Removed {path.relative_to(ROOT)}.")
    if stale:
        sys.exit("out of date: " + ", ".join(stale) + "; run python -m scripts.lean_icg_families")
    if args.check:
        print("Generated Lean certificates are up to date.")


if __name__ == "__main__":
    main()
