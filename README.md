# Solved

A growing collection of mathematical problems, constructions, proof drafts and reproducible checks. Entries are organized by subject and can extend to any area of mathematics.

**Current catalogue:** 34 entries, comprising 29 research proof drafts and 5 finite verification records. Twenty-seven Lean modules include supporting lemmas and complete formalizations of the squaring counterexample, the main additive subtraction-gap theorem, its computable-threshold extension, and the obstruction to marked-root reconstruction. A separate Mathlib project, `formal/` (see the [verification guide](docs/verification.md#mathlib-project)), kernel-checks maximal-energy theorems for integral circulant graphs of order $2^ap^b$, the maximal energy of order $2^ap$ for every $a$, and for orders with two symbolic primes (twenty region theorems, including the prime-dependent maximisers of $2p^2q$ and $2p^3q$). Independent mathematical review remains pending.

[Browse the catalogue](CONTENTS.md) · [Verification guide](docs/verification.md) · [Open questions](docs/open-questions.md) · [Contributing](CONTRIBUTING.md)

## Work awaiting Lean verification (27 November 2026)

These are exact computer certificates in Python. They are **not claimed as results** until each has a Lean formalization and a statement correspondence. That work is in progress.

- [Integral circulant graphs at the primes 2 and 3](results/icg-energy-exceptional-orders/PROOF.md): certificates for 49 order families. The 19 families $3^ap^b$ reproduce known theorems (Jiang–Yang, Dong). No earlier treatment was found for the other 30, which include every even order listed and a ratio-dependent maximiser for $2p^2q$. The 19 families $2^ap^b$ among them are now [Lean-verified](results/icg-energy-even-orders/PROOF.md), and so are the orders with two symbolic primes ([entry](results/icg-energy-two-symbolic-primes/PROOF.md)), including the ratio-dependent maximisers of $2p^2q$ and $2p^3q$.
- [Roldán's conjecture for ICG(p²q³)](results/icg-energy-p2q3/PROOF.md): an independent re-verification of a result already proved by Park, Schreib, Jiang–Yang and Dong.
- [Matroid polynomial checks on q-uniform matroids](results/q-uniform-matroid-checks/PROOF.md): negative evidence on 9,371 matroids for open conjectures.

## Results

<!-- BEGIN GENERATED LEAN STATUS -->

✅ Complete formalization of the entry's stated main claim · 🟡 Checked supporting lemmas · ⬜ No Lean formalization.

| Result | Lean verification |
|---|---|
| [An unbounded additive advantage for subtraction](results/subtraction-gap/PROOF.md) | [✅ Complete](results/subtraction-gap/FORMALIZATION.md) |
| [A counterexample to universal AM squaring stability](results/square-instability/PROOF.md) | [✅ Complete](results/square-instability/FORMALIZATION.md) |
| [Effective cutoffs for square-run arithmetic controls](results/effective-control-cutoffs/PROOF.md) | [✅ Complete](results/effective-control-cutoffs/FORMALIZATION.md) |
| [An obstruction to simultaneous square-root retention](results/root-retention-obstruction/PROOF.md) | [✅ Complete](results/root-retention-obstruction/FORMALIZATION.md) |
| [Maximal-energy integral circulant graphs of order 2^a p^b](results/icg-energy-even-orders/PROOF.md) | [✅ Complete](results/icg-energy-even-orders/FORMALIZATION.md) |
| [Maximal-energy integral circulant graphs with two symbolic primes](results/icg-energy-two-symbolic-primes/PROOF.md) | [✅ Complete](results/icg-energy-two-symbolic-primes/FORMALIZATION.md) |
| [An all-length block classification of two-small-step chains](results/two-small-steps/PROOF.md) | 🟡 Supporting lemmas |
| [The counting exponent at every fixed AM defect](results/fixed-defect-counting/PROOF.md) | 🟡 Supporting lemmas |
| [Well-ordering and global order type of real AM defects](results/am-defect-order/PROOF.md) | 🟡 Supporting lemmas |
| [The proposed sharp type of each bounded AM-defect slice](results/am-defect-slices/PROOF.md) | 🟡 Supporting lemmas |
| [Extremal values and optimal simultaneous cancellation](results/signed-growth/PROOF.md) | 🟡 Supporting lemmas |
| [Unique integer recovery from narrow product intervals](results/narrow-products/PROOF.md) | 🟡 Supporting lemmas |
| [Directed recovery from monotone polynomial intervals](results/directed-monotone-recovery/PROOF.md) | 🟡 Supporting lemmas |
| [Square-root reconstruction in low-defect sectors](results/root-closure-sectors/PROOF.md) | 🟡 Supporting lemmas |
| [At most two assignments from an informative arithmetic cycle](results/informative-cycles/PROOF.md) | ⬜ Not formalized |
| [Complete bounded enumeration of two-small-step AM chains](results/bounded-am-chains/PROOF.md) | ⬜ Not formalized |
| [Exact affine root domains in balanced components](results/affine-domains/PROOF.md) | ⬜ Not formalized |
| [Divisor certificates for nonlinear fractional-linear domains](results/nonlinear-domains/PROOF.md) | ⬜ Not formalized |
| [Twelve squaring rays with seven canonical nonsquares](results/seven-nonsquares/PROOF.md) | ⬜ Not formalized |
| [Infinitely many primitive rays with six nonsquares](results/six-nonsquares/PROOF.md) | ⬜ Not formalized |
| [Sharp counting order for shortest defect-two endpoints](results/two-defect-counting/PROOF.md) | ⬜ Not formalized |
| [Sharp completion and increment bounds from an AM prefix](results/prefix-extrema/PROOF.md) | ⬜ Not formalized |
| [A sharp nonsquare bound for positive arithmetic with arbitrary seeds](results/record-defect/PROOF.md) | ⬜ Not formalized |
| [Exact synthesis by target saturation and helper branching](results/target-saturation/PROOF.md) | ⬜ Not formalized |
| [A complete finite menu for the final helper](results/final-helper/PROOF.md) | ⬜ Not formalized |
| [Product constraints over finite palettes: feasibility and costs](results/product-palettes/PROOF.md) | ⬜ Not formalized |
| [Factor recovery through guarded arithmetic paths](results/guarded-product-paths/PROOF.md) | ⬜ Not formalized |
| [Exact computation costs for the integer 255](results/integer-255/PROOF.md) | ⬜ Not formalized |
| [Exact register requirements for a fixed one-shot DAG](results/one-shot-registers/PROOF.md) | ⬜ Not formalized |
| [Star-chain lifting and finite Scholz–Brauer certificates](results/scholz-finite/PROOF.md) | ⬜ Not formalized |
| [An elementary eventually-periodic case of essential components](results/periodic-essential-components/PROOF.md) | ⬜ Not formalized |
| [Matroid polynomial conjectures on q-uniform matroids with free points](results/q-uniform-matroid-checks/PROOF.md) | ⬜ Not formalized |
| [The maximal-energy divisor set of integral circulant graphs of order p^2q^3](results/icg-energy-p2q3/PROOF.md) | ⬜ Not formalized |
| [Exact certificates for maximal-energy integral circulant graphs at the primes 2 and 3](results/icg-energy-exceptional-orders/PROOF.md) | ⬜ Not formalized |

<!-- END GENERATED LEAN STATUS -->

Each entry has an exact statement, assumptions, manuscript, primary references, executable checks where available, and explicit formalization scope in [catalogue.json](catalogue.json). A successful finite search establishes its stated finite claim. A supporting Lean lemma establishes its formal statement. The ticks refer to the exact claims linked in the table; they do not certify broader conjectures, novelty or independent review. These labels are generated from the catalogue and checked by CI.

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
