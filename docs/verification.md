# Proof scope and reproducibility

## Status vocabulary

| Status | Meaning |
|---|---|
| `open` | A precise question without a claimed proof. |
| `proof-draft` | A written proposed argument, awaiting independent mathematical review. |
| `finite-verification` | Exhaustive or exact evidence for a specified finite set or range. |
| `reviewed-proof` | A written proof with a linked independent review record. |
| `withdrawn` | A claim retained for traceability but no longer asserted. |

Formalization is a separate field: `none`, `supporting-lemmas`, or `complete`. Complete formalization requires an explicit statement correspondence. Independent-review records are pending. The [squaring-instability entry](../results/square-instability/PROOF.md) has a complete formalization of its stated counterexample and infinite construction consequence; other main conjecture arguments remain drafts with supporting lemmas.

## Python checks

Use a fresh Python 3.12+ virtual environment and `python -m pip install -e .`. SymPy is pinned to 1.14.0. No customized package fork or external dataset is required. Arithmetic remains exact; Fraction, integer division and integer roots replace floating-point equality tests.

```sh
python -m scripts.check_catalogue
python -m scripts.verify all
python -m scripts.verify guarded-product-paths
python -m scripts.check_certificates
```

For the pinned formatting and static checks, install `python -m pip install -e ".[dev]"`, then run `ruff check .` and `ruff format --check .`.

The full suite includes exhaustive small assignments, independent operation replay, randomized tests with fixed seeds, empty and inconsistent domains, repeated operands, destructive overwrites, exact-division guards, magnitude boundaries and failed-domain cases. The certificate command independently reproduces all eight stored mathematical records under [checks/expected](../checks/expected/chains.json), including the complete level-12 census. Timing values are excluded from mathematical certificates. Local-link and catalogue validation catch missing evidence paths, inconsistent statuses and dependency cycles. External URLs are not fetched during CI.

Some algorithms are exhaustive and intentionally exponential in their stated parameters. A finite search has the coverage described by its generator and tests. Unsupported instances and resource limits must not be reported as mathematical impossibility.

## Lean checks

Install the [official Lean toolchain](https://lean-lang.org/lean4/doc/quickstart.html) identified in [lean-toolchain](../lean-toolchain), or use that release's `lean` and `lake` binaries on PATH. Run:

```sh
python -m scripts.check_formalization
```

This builds the complete import closure and prints the axiom dependencies of every theorem declaration registered in [formalization.json](formalization.json). It rejects missing theorem reports, unfinished proofs and project-specific axioms. Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are permitted. These are not a claim of axiom-free mathematics.

| Module | What the formal statements cover |
|---|---|
| [SquareInstability](../lean/SquareInstability.lean) | Complete chain-search argument, exact eight-write minima for 267 and its square, and the iterated-square construction. See its [statement correspondence](../results/square-instability/FORMALIZATION.md). |
| [ChainCoverage](../lean/ChainCoverage.lean) | Nonsquare-predecessor marking and reconstruction of gaps between marks in increasing AM chains. |
| [Compression](../lean/Compression.lean) | Common-power compression of ordinary intervals with local multiplication and square runs. |
| [MarkedComparison](../lean/MarkedComparison.lean) | Squared domination after one additional square, including saved-history reads. |
| [FiniteControls](../lean/FiniteControls.lean) | Finite-dimensional thinning and a no-descending-sequence implication. |
| [PositiveExpressions](../lean/PositiveExpressions.lean) | Monotonicity for positive expressions under supplied order assumptions. |
| [TwoSmallBlocks](../lean/TwoSmallBlocks.lean) | Proper-sum and inner-run lag inequalities. |
| [SignedEnvelope](../lean/SignedEnvelope.lean) | A nonmaximal-operation estimate and a record-growth bound. |
| [ProductIntervals](../lean/ProductIntervals.lean) | Narrow-interval transport, unique neighbors and antitone fixed-point uniqueness. |
| [SubtractionGap](../lean/SubtractionGap.lean) | Strict power inequalities, upward-region exclusion, and the finite-family obstruction under supplied domination. |

Complete finite-control packaging, the nonsquare count bound, asymptotic estimates, ordinal conclusions and global graph algorithms remain written mathematics. Read each entry's `formalization.scope` before interpreting its formal evidence. In particular, the subtraction-gap module does not formalize the unbounded additive-separation theorem.

## Audit priorities

For fixed-defect counting, check that every future read inside a long square run is preserved by a marker. For ordinal lower bounds, check the finite coloring by actual shortening: the constructed witnesses need not be shortest. For bounded ordinal slices, check that normalized corrections are locally finite away from zero and that a proper initial segment bounds at least one reset parameter. For the additive gap, check normalization, bounded nonsquare count and finite-control coverage before applying Dickson's lemma.

For arithmetic domains, check every executed prefix. Algebraic cancellation does not erase exact divisibility or an intermediate magnitude limit. For register statements, distinguish one-shot execution from recomputation and specify initial occupancy, destructive overwrites, target visits and exit pins.

## Provenance

The mathematical material was reorganized into a standalone collection on 26 November 2026. [import-record.json](import-record.json) stores digests of original verification sources before namespace and dependency extraction. Each manuscript's catalogue entry records its source digest. These identify the import inputs; they are not hashes of the edited public files or proof certificates. Git records the public versions. Expected mathematical outputs are regenerated by the commands above.

Source URLs carry their catalogue-record date, not a claim that every later paper has been surveyed. The initial literature review examined primary sources on 25–26 November 2026. Research drafts should retain their status until review resolves correctness and scope.
