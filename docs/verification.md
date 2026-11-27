# Proof scope and reproducibility

## Status vocabulary

| Status | Meaning |
|---|---|
| `open` | A precise question without a claimed proof. |
| `proof-draft` | A written proposed argument, awaiting independent mathematical review. |
| `finite-verification` | Exhaustive or exact evidence for a specified finite set or range. |
| `reviewed-proof` | A written proof with a linked independent review record. |
| `withdrawn` | A claim retained for traceability but no longer asserted. |

The README displays ✅ for a completely formalized main claim, 🟡 for checked supporting lemmas, and ⬜ when there is no Lean formalization. Its table is generated from `catalogue.json`; `python -m scripts.check_catalogue --write-index` refreshes it, and CI rejects stale labels. Complete ticks link to the statement correspondence.

Formalization is a separate field: `none`, `supporting-lemmas`, or `complete`. Complete formalization requires an explicit statement correspondence. Independent-review records are pending. The [squaring-instability entry](../results/square-instability/PROOF.md), the [main additive subtraction-gap theorem](../results/subtraction-gap/PROOF.md), its [computable-threshold extension](../results/effective-control-cutoffs/PROOF.md), and the [marked-root obstruction](../results/root-retention-obstruction/PROOF.md) have complete formalizations of their stated main claims. Their written presentations and publication priority still await independent review.

## Python checks

Use a fresh Python 3.12+ virtual environment and `python -m pip install -e .`. SymPy is pinned to 1.14.0. No customized package fork or external dataset is required. Arithmetic remains exact; Fraction, integer division and integer roots replace floating-point equality tests.

```sh
python -m scripts.check_catalogue
python -m scripts.verify all
python -m scripts.verify guarded-product-paths
python -m scripts.check_certificates
```

For the pinned formatting and static checks, install `python -m pip install -e ".[dev]"`, then run `ruff check .` and `ruff format --check .`.

The full suite includes exhaustive small assignments, independent operation replay, randomized tests with fixed seeds, empty and inconsistent domains, repeated operands, destructive overwrites, exact-division guards, magnitude boundaries and failed-domain cases. The certificate command independently reproduces every stored mathematical record under [checks/expected](../checks/expected/chains.json), including the complete level-12 census. Timing values are excluded from mathematical certificates. Local-link and catalogue validation catch missing evidence paths, inconsistent statuses and dependency cycles. External URLs are not fetched during CI.

Some algorithms are exhaustive and intentionally exponential in their stated parameters. A finite search has the coverage described by its generator and tests. Unsupported instances and resource limits must not be reported as mathematical impossibility.

## Lean checks

Install the [official Lean toolchain](https://lean-lang.org/lean4/doc/quickstart.html) identified in [lean-toolchain](../lean-toolchain), or use that release's `lean` and `lake` binaries on PATH. Run:

```sh
python -m scripts.check_formalization
```

This builds the complete import closure and prints the axiom dependencies of every theorem declaration registered in [formalization.json](formalization.json). It rejects missing theorem reports, unfinished proofs and project-specific axioms. Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are permitted. These are not a claim of axiom-free mathematics. The command also kernel-checks the [Python/Lean profile comparison](../checks/verify_profile_formalization.py) on 779 profiles, 1,558 endpoints and 3,073 box decisions. This finite comparison is separate from the universal arithmetic oracle proof. A second checker compares compiled execution of the proved Lean basis function against Python on 1,551 cases; its finite outputs are execution evidence, not kernel-evaluated equality proofs. UniversalCutoff component checks add 10,640 kernel-checked clipping/cost assertions, six small finite aggregates and six guard cases. They never evaluate the universal threshold itself.

| Module | What the formal statements cover |
|---|---|
| [SquareInstability](../lean/SquareInstability.lean) | Complete chain-search argument, exact eight-write minima for 267 and its square, and the iterated-square construction. See its [statement correspondence](../results/square-instability/FORMALIZATION.md). |
| [BoundedControls](../lean/BoundedControls.lean) | Bounded control fields, Dickson comparison and the eventual Mersenne lower bound for increasing AM chains. |
| [AMNormalization](../lean/AMNormalization.lean) | Arbitrary AM programs normalize to increasing chains without increasing cost; the lower bound transfers. |
| [AdditiveSeparation](../lean/AdditiveSeparation.lean) | Integer signed constructions, minimum-cost existence and uniqueness, and the full main additive-gap conclusion. |
| [MarkedEncoding](../lean/MarkedEncoding.lean) | Every increasing AM chain has legal marked code preserving its endpoint and exact write count, with bounded size and operand addresses. |
| [NonsquareBound](../lean/NonsquareBound.lean) | Integer Fibonacci envelopes from the initial seed or an arbitrary prefix, canonical step counting, the bound p≤4s+4 and a two-nonsquare cubic barrier. |
| [ControlInflation](../lean/ControlInflation.lean) | Comparable control programs, exact cost differences, and domination by the corresponding iterated square. |
| [EffectiveCutoffs](../lean/EffectiveCutoffs.lean) | Integer ratio witnesses and leading-profile upper/lower decisions. |
| [DiagonalProfiles](../lean/DiagonalProfiles.lean) | Whole-program coefficient profiles, saved-history invariants, exact cost correspondence and the complete diagonal criterion. |
| [IdealOracle](../lean/IdealOracle.lean) | Box cofinality, Boolean ideal-intersection decisions and computed witnesses. |
| [FiniteLists](../lean/FiniteLists.lean) | Shared list membership and duplicate-removal facts. |
| [FiniteBasis](../lean/FiniteBasis.lean) | A total recursive reference search, strict box-rank descent, exact coverage and minimal-generator pruning. |
| [ArithmeticBasis](../lean/ArithmeticBasis.lean) | Complete basis membership, exact-solution inclusion and safe per-domain cutoffs using the concrete arithmetic oracle. |
| [RootSectorLemmas](../lean/RootSectorLemmas.lean) | Elementary square gaps, power-of-two factors, a complete three-operation/four-operation exchange identity, and paired-cofactor/boundary-square identities and universal first-big-prefix growth inequalities and two explicit GSGG source/root programs supporting the partial root-closure result. |
| [RootRetention](../lean/RootRetention.lean) | Complete marked-search argument, exact costs 6/7/7 for 2000, its square, and the joint requirement {10,2000}; a shortest defect-two source refutes uniform marked-root reconstruction. |
| [PowerChainLift](../lean/PowerChainLift.lean) | A valid AM chain from any increasing addition-only chain, with the initial 2 write charged and the endpoint/root identity proved. The low-step classification and exponent extraction remain outside this formalization. |
| [UniversalCutoff](../lean/UniversalCutoff.lean) | Finite clipping/control coverage and a computable universal threshold for arbitrary AM programs and the additive subtraction gap. |
| [DirectedRecovery](../lean/DirectedRecovery.lean) | Agreement along functional paths and uniqueness under signed-cycle and seed coverage, given certified transport hypotheses. |
| [ChainCoverage](../lean/ChainCoverage.lean) | Nonsquare-predecessor marking and reconstruction of gaps between marks in increasing AM chains. |
| [Compression](../lean/Compression.lean) | Common-power compression of ordinary intervals with local multiplication and square runs. |
| [MarkedComparison](../lean/MarkedComparison.lean) | Squared domination after one additional square, including saved-history reads. |
| [FiniteControls](../lean/FiniteControls.lean) | Finite-dimensional thinning and a no-descending-sequence implication. |
| [PositiveExpressions](../lean/PositiveExpressions.lean) | Monotonicity for positive expressions under supplied order assumptions. |
| [TwoSmallBlocks](../lean/TwoSmallBlocks.lean) | Proper-sum and inner-run lag inequalities. |
| [SignedEnvelope](../lean/SignedEnvelope.lean) | A nonmaximal-operation estimate and a record-growth bound. |
| [ProductIntervals](../lean/ProductIntervals.lean) | Narrow-interval transport, unique neighbors and antitone fixed-point uniqueness. |
| [SubtractionGap](../lean/SubtractionGap.lean) | Strict power inequalities, upward-region exclusion, a finite-family obstruction, and the concrete Mersenne-program antichain theorem. |

The main additive-gap dependency chain is now formalized through the asymptotic conclusion. Ordinal-type conclusions, the other separation families and concrete polynomial recovery retain the scopes stated in their entries. The nonsquare count bound and comparable-program cost domination now have universal integer proofs. Read each entry's `formalization.scope` before interpreting its formal evidence. The earlier SubtractionGap module contains intermediate lemmas; the final unbounded theorem is in AdditiveSeparation and is mapped to the mathematical statement in its [correspondence document](../results/subtraction-gap/FORMALIZATION.md).

## Audit priorities

For fixed-defect counting, check that every future read inside a long square run is preserved by a marker. For ordinal lower bounds, check the finite coloring by actual shortening: the constructed witnesses need not be shortest. For bounded ordinal slices, check that normalized corrections are locally finite away from zero and that a proper initial segment bounds at least one reset parameter. For the additive gap, check normalization, bounded nonsquare count and finite-control coverage before applying Dickson's lemma.

For arithmetic domains, check every executed prefix. Algebraic cancellation does not erase exact divisibility or an intermediate magnitude limit. For register statements, distinguish one-shot execution from recomputation and specify initial occupancy, destructive overwrites, target visits and exit pins.

## Provenance

The mathematical material was reorganized into a standalone collection on 26 November 2026. [import-record.json](import-record.json) stores digests of original verification sources before namespace and dependency extraction. Each manuscript's catalogue entry records its source digest. These identify the import inputs; they are not hashes of the edited public files or proof certificates. Git records the public versions. Expected mathematical outputs are regenerated by the commands above.

Source URLs carry their catalogue-record date, not a claim that every later paper has been surveyed. The initial literature review examined primary sources on 25–26 November 2026. Research drafts should retain their status until review resolves correctness and scope.
