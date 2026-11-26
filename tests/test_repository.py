import copy
import json
import tempfile
import unittest
from pathlib import Path

from scripts.check_catalogue import ROOT, check_links, contents, unique_object, validate
from scripts.check_formalization import parse_axioms


class RepositoryTests(unittest.TestCase):
    def setUp(self):
        self.data = json.loads((ROOT / "catalogue.json").read_text())

    def test_catalogue_and_navigation(self):
        entries = validate(self.data, ROOT)
        self.assertEqual((ROOT / "CONTENTS.md").read_text(), contents(entries))
        check_links(ROOT)

    def test_invalid_metadata(self):
        mutations = [
            lambda d: d["entries"].append(copy.deepcopy(d["entries"][0])),
            lambda d: d["entries"][0].update(status="accepted-without-review"),
            lambda d: d["entries"][0].update(status="reviewed-proof"),
            lambda d: d["entries"][0].update(review="independently-reviewed"),
            lambda d: d["entries"][0].update(proof="../exterior.md"),
            lambda d: d["entries"][0].update(tests=["test_missing.py"]),
            lambda d: d["entries"][0].update(dependencies=["absent"]),
            lambda d: d["entries"][0].update(dependencies=[d["entries"][0]["id"]]),
            lambda d: d["entries"][0].update(sources=[{"url": "file:///exterior"}]),
            lambda d: d["entries"][0]["formalization"].update(
                status="complete", files=["lean/Compression.lean"]
            ),
            lambda d: d["entries"][0]["formalization"].update(
                status="none", files=["lean/Compression.lean"]
            ),
            lambda d: d["entries"][0].update(status="finite-verification", tests=[]),
        ]
        for change in mutations:
            data = copy.deepcopy(self.data)
            change(data)
            with self.assertRaises(ValueError):
                validate(data, ROOT)
        with self.assertRaises(ValueError):
            json.loads('{"a": 1, "a": 2}', object_pairs_hook=unique_object)

    def test_complete_formalization_names_the_actual_statements(self):
        for names in (
            None,
            [],
            ["SolvedInstability.absent"],
            ["SolvedControls.no_descending"],
            [True],
        ):
            data = copy.deepcopy(self.data)
            entry = next(e for e in data["entries"] if e["id"] == "square-instability")
            entry["formalization"]["theorems"] = names
            with self.assertRaises(ValueError):
                validate(data, ROOT)

    def test_missing_and_external_local_links(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            p = root / "README.md"
            p.write_text(
                "[ok](https://example.org) [self](README.md)\n```sh\n[code](missing)\n```\n"
            )
            check_links(root)
            for link in ("missing.md", "../outside.md"):
                p.write_text(f"[bad]({link})\n")
                with self.assertRaises(ValueError):
                    check_links(root)

    def test_axiom_audit_is_complete_and_rejects_untrusted_axioms(self):
        output = "'A.one' depends on axioms: [propext, Quot.sound]\n'A.two' does not depend on any axioms\n"
        self.assertEqual(parse_axioms(output, ["A.one", "A.two"])["A.two"], [])
        for invalid in (
            output.replace("Quot.sound", "sorryAx"),
            output.replace("Quot.sound", "Project.guess"),
            output.splitlines()[0],
            output + output,
        ):
            with self.assertRaises(ValueError):
                parse_axioms(invalid, ["A.one", "A.two"])
