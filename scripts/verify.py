"""Run the executable tests associated with one catalogue entry."""

import argparse
import json
import subprocess
import sys

from scripts.check_catalogue import ROOT, validate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("entry", help="catalogue id, or 'all' for the complete test suite")
    args = parser.parse_args()
    entries = validate(json.loads((ROOT / "catalogue.json").read_text()), ROOT)
    if args.entry == "all":
        patterns = ["test_*.py"]
    else:
        selected = next((entry for entry in entries if entry["id"] == args.entry), None)
        if selected is None:
            parser.error("unknown entry; see CONTENTS.md")
        print(selected["formalization"]["scope"], flush=True)
        patterns = selected["tests"]
        if not patterns:
            print("No executable check is registered for this written result.")
    for pattern in patterns:
        subprocess.run(
            [
                sys.executable,
                "-B",
                "-m",
                "unittest",
                "discover",
                "-s",
                "tests",
                "-p",
                pattern,
                "-v",
            ],
            cwd=ROOT,
            check=True,
        )
    print("These checks cover their stated finite cases; proof status is unchanged.")


if __name__ == "__main__":
    main()
