"""Write the generated Lean energy certificates, or check that they are up to date (--check).

Outputs formal/Formal/ICG/EvenFamilies.lean (certificates and graph-energy theorems) and
formal/FormalTests/Axioms.lean (axiom audit), from checks/expected/icg-families.json.
"""

import argparse
import sys

from scripts.check_catalogue import ROOT
from solved.lean_icg import axioms_from, render_from

SOURCE = ROOT / "checks" / "expected" / "icg-families.json"
TARGETS = {
    ROOT / "formal" / "Formal" / "ICG" / "EvenFamilies.lean": render_from,
    ROOT / "formal" / "FormalTests" / "Axioms.lean": axioms_from,
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
    if stale:
        sys.exit("out of date: " + ", ".join(stale) + "; run python -m scripts.lean_icg_families")
    if args.check:
        print("Generated Lean certificates are up to date.")


if __name__ == "__main__":
    main()
