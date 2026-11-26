# Contributing mathematical work

Start by checking the catalogue, implementations and cited literature for an existing result or equivalent method. Use primary sources and record the exact version or section relevant to a claim.

A new entry needs:

1. A precise question and statement, including the domain, quantifiers and exceptional cases.
2. A self-contained argument or a clearly identified gap, with attribution for existing results.
3. The distinction between a new theorem, a known special case, a finite verification and an open problem.
4. Reproducible checks that test meaningful alternatives or boundary cases, where computation applies.
5. Explicit proof-assistant scope and an independent-review record when either is claimed.

Put the manuscript at `results/<id>/PROOF.md` and add its metadata to `catalogue.json`. Subjects are free-form; add areas as the research expands. Use the existing status vocabulary documented in [the verification guide](docs/verification.md). Dependencies name other catalogue IDs. A full formalization must include a written correspondence between its theorem statement and the manuscript statement. Independent review needs a public, attributable record; an agent's self-review does not qualify.

Run `python -m scripts.check_catalogue --write-index` after changing the catalogue. Run the relevant tests, the complete suite before publishing, and the formal checks whenever a formal module or its dependencies change. Update expected certificates only after explaining and verifying the mathematical reason for a change. Keep withdrawn or corrected claims traceable in Git history and mark their current status clearly.

Keep entries independent of a particular downstream application. Include mathematical examples and self-contained verification inputs; operational datasets, private logs, local machine paths and application-specific experiments belong elsewhere.

External references remain owned by their authors. Link and attribute them; do not import third-party manuscripts without suitable permission. Disclose AI assistance. Do not call a conjecture resolved solely because examples, a search, or related lemmas pass.
