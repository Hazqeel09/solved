# Solved

A growing collection of mathematical problems, constructions, proof drafts and reproducible checks. Entries are organized by subject and can extend to any area of mathematics.

**Current catalogue:** 26 entries, comprising 22 research proof drafts and 4 finite verification records. Fourteen Lean modules include supporting lemmas and one complete formalization of a stated counterexample. Independent mathematical review remains pending.

[Browse the catalogue](CONTENTS.md) · [Verification guide](docs/verification.md) · [Open questions](docs/open-questions.md) · [Contributing](CONTRIBUTING.md)

## Selected work

| Topic | Precise scope |
|---|---|
| [Squaring instability](results/square-instability/PROOF.md) | A fully formalized counterexample: 267 and its square both have minimum cost eight. |
| [Two-small-step addition–multiplication chains](results/two-small-steps/PROOF.md) | An all-length block classification manuscript, with independent finite enumeration. |
| [Real arithmetic-chain defects](results/am-defect-order/PROOF.md) | Proposed well-ordering and global ordinal type, with a separate [bounded-slice argument](results/am-defect-slices/PROOF.md). |
| [Subtraction and computation length](results/subtraction-gap/PROOF.md) | A proposed unbounded **additive** separation. Polynomial equivalence remains a separate question. |
| [Integer factor recovery](results/narrow-products/PROOF.md) | A sharp interval-width condition, exact graph reconstruction, [finite-palette complexity](results/product-palettes/PROOF.md), and [directed nonlinear recovery](results/directed-monotone-recovery/PROOF.md). |
| [Essential components](results/periodic-essential-components/PROOF.md) | An elementary eventually-periodic case; the general problem remains outside this result. |

Each entry has an exact statement, assumptions, manuscript, primary references, executable checks where available, and explicit formalization scope in [catalogue.json](catalogue.json). A successful finite search establishes its stated finite claim. A supporting Lean lemma establishes its formal statement. Neither changes the review status of a broader manuscript.

## Reproduce

Use Python 3.12 or newer and Lean 4.8.0. From a fresh checkout:

```sh
python3 -m venv .venv
. .venv/bin/activate
python -m pip install -e .
python -m scripts.check_catalogue
python -m scripts.verify all
python -m scripts.check_certificates
python -m scripts.check_formalization
```

The Python checks need only the dependency declared in [pyproject.toml](pyproject.toml). The Lean library uses Lean core. Installation, expected evidence and audit limitations are described in the [verification guide](docs/verification.md). CI runs the same checks.

## Layout

- `results/`: self-contained mathematical manuscripts.
- `catalogue.json` and `CONTENTS.md`: structured records and generated navigation.
- `solved/`, `checks/` and `tests/`: exact arithmetic implementations, independent enumerations and differential tests.
- `lean/`: formal lemmas, with a [theorem registry](docs/formalization.json).
- `docs/`: evidence standards, open questions and provenance.

This collection uses the [MIT license](LICENSE). Its catalogue-and-verification organization takes inspiration from [1337isnot1337/solved-conjectures](https://github.com/1337isnot1337/solved-conjectures). That reference is organizational inspiration, not mathematical evidence. The initial research was developed with assistance from OpenAI Codex and Anthropic Claude; independent mathematical review is pending.
