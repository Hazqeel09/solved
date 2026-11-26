"""Validate research metadata, references and generated navigation."""

import argparse
import json
import re
from pathlib import Path
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parents[1]
STATUSES = {"open", "proof-draft", "finite-verification", "reviewed-proof", "withdrawn"}


def local_file(root, name):
    if not isinstance(name, str) or not name or Path(name).is_absolute():
        raise ValueError(f"invalid relative file: {name!r}")
    path = (root / name).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError(f"missing or exterior file: {name}")
    return path


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def validate(data, root):
    if not isinstance(data, dict) or data.get("schema_version") != 1:
        raise ValueError("expected catalogue schema version 1")
    entries = data.get("entries")
    if not isinstance(entries, list) or not entries:
        raise ValueError("expected nonempty entry list")
    by_id = {}
    for item in entries:
        if not isinstance(item, dict):
            raise ValueError("entry must be an object")
        slug = item.get("id", "")
        if not re.fullmatch(r"[a-z][a-z0-9]*(?:-[a-z0-9]+)*", slug) or slug in by_id:
            raise ValueError(f"invalid or duplicate id: {slug}")
        by_id[slug] = item
        for key in ("title", "subject", "statement"):
            if not isinstance(item.get(key), str) or not item[key].strip():
                raise ValueError(f"{slug}: missing {key}")
        if item.get("status") not in STATUSES:
            raise ValueError(f"{slug}: invalid status")
        if item.get("review") not in {"independent-review-pending", "independently-reviewed"}:
            raise ValueError(f"{slug}: invalid review state")
        reviewed = item["review"] == "independently-reviewed"
        if reviewed and not item.get("review_links"):
            raise ValueError(f"{slug}: independent review needs a public record")
        if item["status"] == "reviewed-proof" and not reviewed:
            raise ValueError(f"{slug}: reviewed proof needs independent review")
        if item.get("proof") != f"results/{slug}/PROOF.md":
            raise ValueError(f"{slug}: proof path must match id")
        local_file(root, item["proof"])
        for key in ("tests", "implementation", "dependencies", "sources"):
            if not isinstance(item.get(key), list):
                raise ValueError(f"{slug}: {key} must be a list")
        for test in item["tests"]:
            if not re.fullmatch(r"test_[a-z_]+\.py", test):
                raise ValueError(f"{slug}: invalid test file")
            local_file(root, f"tests/{test}")
        for name in item["implementation"]:
            local_file(root, name)
        if item["status"] == "finite-verification" and not item["tests"]:
            raise ValueError(f"{slug}: finite verification needs executable checks")
        formal = item.get("formalization")
        if not isinstance(formal, dict) or not formal.get("scope"):
            raise ValueError(f"{slug}: formalization needs a scope")
        if formal.get("status") not in {"none", "supporting-lemmas", "complete"}:
            raise ValueError(f"{slug}: invalid formalization state")
        files = formal.get("files")
        if not isinstance(files, list) or bool(files) != (formal["status"] != "none"):
            raise ValueError(f"{slug}: inconsistent formalization files")
        for name in files:
            local_file(root, name)
        if formal["status"] == "complete" and not formal.get("statement_correspondence"):
            raise ValueError(f"{slug}: complete formalization needs a statement correspondence")
        if formal.get("statement_correspondence"):
            local_file(root, formal["statement_correspondence"])
        if not item["sources"]:
            raise ValueError(f"{slug}: primary references are required")
        for source in item["sources"]:
            parts = urlsplit(source.get("url", ""))
            if parts.scheme != "https" or not parts.netloc:
                raise ValueError(f"{slug}: invalid source URL")
    active, finished = set(), set()

    def visit(slug):
        if slug not in by_id:
            raise ValueError(f"missing dependency: {slug}")
        if slug in active:
            raise ValueError(f"cyclic dependency: {slug}")
        if slug in finished:
            return
        active.add(slug)
        for dependency in by_id[slug]["dependencies"]:
            visit(dependency)
        active.remove(slug)
        finished.add(slug)

    for slug in by_id:
        visit(slug)
    actual = {p.relative_to(root).as_posix() for p in (root / "results").glob("*/PROOF.md")}
    if actual != {item["proof"] for item in entries}:
        raise ValueError("every manuscript must have exactly one catalogue entry")
    return entries


def check_links(root):
    # Repository prose uses inline links. External references are recorded, not fetched in CI.
    for path in root.rglob("*.md"):
        if any(part.startswith(".") for part in path.relative_to(root).parts):
            continue
        text = re.sub(r"```.*?```", "", path.read_text(), flags=re.S)
        for target in re.findall(r"\]\(([^\s)]+)\)", text):
            parts = urlsplit(target.strip("<>"))
            if parts.scheme or not parts.path:
                continue
            referenced = (path.parent / unquote(parts.path)).resolve()
            if not referenced.is_relative_to(root.resolve()) or not referenced.is_file():
                raise ValueError(f"{path.relative_to(root)}: broken local link {target}")


def contents(entries):
    rows = [
        "# Contents",
        "",
        "Generated from [catalogue.json](catalogue.json). Status describes the main statement; formalization may cover only supporting lemmas.",
        "",
    ]
    for subject in sorted({entry["subject"] for entry in entries}):
        rows.extend([f"## {subject}", "", "| Result | Status | Formalization |", "|---|---|---|"])
        for entry in entries:
            if entry["subject"] == subject:
                rows.append(
                    f"| [{entry['title']}]({entry['proof']}) | {entry['status']} | {entry['formalization']['status']} |"
                )
        rows.append("")
    return "\n".join(rows)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write-index", action="store_true")
    args = parser.parse_args()
    data = json.loads((ROOT / "catalogue.json").read_text(), object_pairs_hook=unique_object)
    entries = validate(data, ROOT)
    generated = contents(entries)
    path = ROOT / "CONTENTS.md"
    if args.write_index:
        path.write_text(generated)
    elif not path.is_file() or path.read_text() != generated:
        raise ValueError("CONTENTS.md is stale; run with --write-index")
    check_links(ROOT)
    print(f"Validated {len(entries)} entries, dependency graph and local Markdown links.")


if __name__ == "__main__":
    main()
