"""Build every Lean module and audit all registered theorem axiom dependencies."""

import json
import re
import subprocess
import tempfile
from pathlib import Path

from checks.verify_profile_formalization import verify as verify_profile_models
from scripts.check_catalogue import ROOT, local_file

ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REPORT = re.compile(
    r"^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)$", re.M
)


def parse_axioms(output, expected):
    seen = {}
    for name, axioms in REPORT.findall(output):
        if name in seen:
            raise ValueError(f"duplicate axiom report: {name}")
        found = {part.strip() for part in axioms.split(",") if part.strip()}
        if found - ALLOWED_AXIOMS:
            raise ValueError(f"unapproved axiom dependencies for {name}: {found}")
        seen[name] = sorted(found)
    if set(seen) != set(expected):
        raise ValueError("axiom audit does not cover exactly the registered theorems")
    return seen


def main():
    manifest = json.loads((ROOT / "docs/formalization.json").read_text())
    names = []
    for module in manifest["modules"]:
        path = local_file(ROOT, module["file"])
        source = path.read_text()
        if re.search(r"\b(?:sorry|admit|axiom)\b", source):
            raise ValueError(f"unfinished proof or project axiom in {module['file']}")
        namespaces = re.findall(r"^namespace ([A-Za-z_][\w.]*)$", source, re.M)
        if len(namespaces) != 1:
            raise ValueError("update audit for a module with nested or multiple namespaces")
        declared = [
            f"{namespaces[0]}.{name}" for name in re.findall(r"^theorem (\w+)", source, re.M)
        ]
        if declared != module["theorems"]:
            raise ValueError(f"theorem registry is stale: {module['file']}")
        names.extend(declared)
    if len(set(names)) != len(names):
        raise ValueError("duplicate registered theorem")
    files = {module["file"] for module in manifest["modules"]}
    actual = {
        p.relative_to(ROOT).as_posix()
        for p in (ROOT / "lean").glob("*.lean")
        if p.name != "Verification.lean"
    }
    if files != actual:
        raise ValueError("every formal module must be registered")
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    if toolchain != manifest["toolchain"]:
        raise ValueError("toolchain and registry disagree")
    version = subprocess.run(
        ["lake", "env", "lean", "--version"], cwd=ROOT, check=True, capture_output=True, text=True
    ).stdout
    if f"version {toolchain.rsplit(':v', 1)[1]}," not in version:
        raise ValueError(f"wrong Lean compiler: {version.strip()}")
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    with tempfile.TemporaryDirectory(prefix="solved-axioms-") as directory:
        audit = Path(directory) / "Audit.lean"
        audit.write_text(
            "import Verification\n" + "".join(f"#print axioms {name}\n" for name in names)
        )
        result = subprocess.run(
            ["lake", "env", "lean", str(audit)],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
        )
    report = parse_axioms(result.stdout, names)
    print(
        f"Audited {len(report)} theorem declarations across {len(files)} modules with {version.strip()}."
    )
    print("Only Lean's standard propext, Classical.choice and Quot.sound axioms are permitted.")
    print("This checks the registered statements; catalogue proofs retain their documented scope.")
    comparison = verify_profile_models()
    print("Kernel-checked Python/Lean model comparison: " + json.dumps(comparison, sort_keys=True))


if __name__ == "__main__":
    main()
