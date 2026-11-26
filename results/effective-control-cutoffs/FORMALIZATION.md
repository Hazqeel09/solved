# Formal scope of the effective cutoff construction

The arithmetic ideal-intersection oracle now has an end-to-end Lean proof.
The complete finite-basis algorithm and the universal computable-cutoff
corollary remain outside that formalization. The entry therefore retains
its supporting-lemmas formalization status and proof-draft review status.
Independent review and publication-priority assessment remain pending.

## Exact checked decision

SolvedIdeal.decision is a concrete Boolean-valued function of a finite
list of constraints and a nonnegative excess. The theorem
SolvedIdeal.decision_correct states, for every such box and excess,

    Nonempty box →
    excess ≤ cost (diagonal box 0) →
    (decision box excess = true ↔ Meets box excess).

Each constraint is an addition, multiplication, bounded square run, or
unbounded square run. Addition and multiplication keep their operand
addresses fixed. A bounded run permits all integer counts in [lo,hi].
An unbounded run permits all counts at least lo. Nonempty requires
positive lower bounds, consistent finite intervals, and the same
conditions recursively for every run.

Inside fixes the control structure and all operand addresses. Meets
means that there exists an Inside program with primitive write count r
satisfying r≥excess and output

    E ≤ 2^(2^(r−excess))−1.

The cost charges a square run of g squarings exactly g writes. The target
index is never obtained by silently truncating a negative integer:
the Hits predicate explicitly requires r≥excess. The theorem needs
this inequality at the anchor. The Python box API has the stronger
precondition that it already holds at the lower corner.

The diagonal fixes bounded coordinates at their upper endpoints and
increases every unbounded coordinate by the same nonnegative t. For a
finite box the decision evaluates its greatest point. Otherwise it
compares the computed leading profile coefficient with the anchor
target plus one.

## Arithmetic interpretation and indexing

The proof uses the existing SolvedMarked interpreter and
SolvedInflation cost function. The initial history supplies the sole
constant 1. Addresses count backward from the newest saved result.
For a legal program after i blocks, addresses 0 through i select the
saved values. The formal evaluator extends the history with additional
copies of 1, so the theorem also covers larger addresses under that
explicit extended-history semantics. No claim that larger addresses
are legal in the Python representation is made.

Every valid Python control embeds in this model. Python numbers marks
forward from the original 1: an operand with absolute mark number a,
used after i previous blocks, becomes Lean history address i−a.
The executable comparison checks that conversion against endpoint
evaluation as well as symbolic coefficients.

No magnitude limit, destructive register operation, subtraction, division,
zero input, negative input or free exponentiation is added. Shared reads,
duplicate results, unused instructions and values decreasing relative
to earlier writes are included. The universal profile theorem even
permits zero anchored square counts; the box theorem's positive lower
bounds restrict its instantiated runs to the stated model.

## Proof chain

| Claim | Checked declarations |
|---|---|
| Finite products and monomial arithmetic | SolvedProfiles.product_mono, product_power, monomial_multiply, monomial_power, monomial_shift |
| Coefficient shape and positivity | shape_add, shape_multiply, shape_power, shape_shift |
| Upper and lower bounds through each operation | bound_add, bound_multiply, bound_power, bound_shift |
| Old saved values remain valid after another free run | bound_promote, history_promote |
| Whole-program profile extraction, with no supplied profile bounds | build_bound, build_dimension, program_profile |
| Collecting all lower-degree factors | monomial_collect |
| A computable diagonal witness and exact leading-coefficient criterion | diagonal_criterion, using SolvedEffective.integer_ratio_witness |
| Every unbounded run contributes its exact primitive cost | concrete_cost, diagonal_target, SolvedIdeal.diagonal_index |
| Diagonal witnesses satisfy the original box constraints | diagonal_inside |
| Every box member is below a suitable diagonal program | inside_erasure, inside_below |
| Membership propagates to a larger parameter vector | hits_upward, using the existing comparable-program domination proof |
| No solutions are missed by the diagonal test | meets_iff_diagonal, ideal_criterion |
| Correctness of the concrete Boolean decision | decision_correct |

The finite coefficient vector is represented in Lean by a coefficient
function with a proved support bound and a cached constant-profile flag.
Its value is a finite product over degrees zero through d. The critical
lower bound uses the coefficient at **all free runs processed in the
program prefix**, including runs unused by the output. It does not use
the possibly smaller degree of the output expression.

All earlier saved profiles remain in the induction invariant. At a new
free run, their new top coefficient is 1, so positivity proves their
lower bounds at the enlarged dimension. This is what permits arbitrary
sharing without assuming an expression-tree topology.

## Implementation comparison and limits

The Python implementation trims trailing coefficient ones, skips
arithmetic for unused output ancestors, uses integer ceiling-logarithm
shortcuts, and enforces optional resource budgets. These are executable
refinements, not themselves a universal formal refinement proof.

The checker generates Lean propositions from all 765 annotated controls
of at most three blocks, plus 14 profiles from larger shared controls.
Lean's kernel verifies 779 coefficient vectors and dimensions,
1,558 concrete endpoints, and 3,073 ideal decisions against exact Python
outputs. The cases include every fixed/free assignment in the small
control family, empty programs, shared operands, constant values
recomputed after free runs, and zero-dimensional boxes. This is finite
model-conformance evidence; it is not used in the universal proof.

Run the full formal audit with:

    python -m scripts.check_formalization

It builds the modules, audits every registered theorem's axiom
dependencies, and runs the generated model comparison. The comparison
uses ordinary kernel-checked decide proofs, not native_decide.
Only Lean's standard propext, Classical.choice and Quot.sound are
permitted by the audit.

The remaining unformalized steps are residual-box subtraction and
complete minimal-basis enumeration, its termination and executable
refinement, and the assembly of finitely many control cutoffs into a
universal computable threshold. The latter can use the already checked
normalization, nonsquare-count and marked-encoding theorems; those
coverage results do not need to be assumed or reconstructed.
