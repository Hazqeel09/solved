# Formal scope of the effective cutoff construction

The stated main claims have complete Lean formalizations, including the
universal computable-threshold construction. The reference functions compute
ideal witnesses, complete minimal bases, domain cutoffs, a finite cover and
the final universal threshold. Proof-draft review status remains unchanged:
independent mathematical review and publication-priority assessment are pending.

## Universal conclusion

SolvedUniversal.threshold is a concrete computable function from natural
numbers to natural numbers. effective_program_bound proves:

    threshold C ≤ n →
    program.value r = 2^(2^n)−1 →
    n+C < r

for every nonnegative C,n,r and every SolvedNormalization.Program r.
This is the general AM model, allowing repeated values, decreasing writes
and unused overshoots. Its initial value is 1; every instruction is an
addition or multiplication of earlier results. Cost counts instructions,
with unrestricted retention and no magnitude cap.

effective_additive_gap further proves:

    threshold (C+2) ≤ n →
    MinimumAM (2^(2^n)−1) a →
    MinimumSLP (2^(2^n)−1) b →
    b+C < a.

The signed model permits zero and negative intermediate integers.
effective_minima includes existence of both minimum costs in its conclusion.
It reuses the existing signed construction and minimum-cost existence proof;
the new universal threshold does not assume the earlier qualitative
eventual-gap theorem.

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

## Complete basis computation for one lower corner

SolvedBasis.explore is an ordinary computable Lean definition. It queries a
box, keeps a witness if one exists, and recursively processes every slice
below that witness in one coordinate. SolvedBasis.cut_rank proves that each
recursive call strictly decreases the lexicographic natural-number pair

    (number of infinite upper bounds, sum of finite upper bounds).

This is the termination measure accepted by Lean, not an assumption about
a finite search horizon. SolvedBasis.cut_subset, cut_avoids and cut_covers
establish exact coverage of the complement of the witness's upward orthant.
search_spec proves soundness and coverage of the recursive search.
pruning_covers and basis_spec prove that removing duplicates and dominated
points preserves coverage and leaves minimal generators.

The generic engine takes a sound, complete witness oracle. That interface
is fully instantiated in SolvedArithmeticBasis.oracle using the proved
arithmetic oracle. SolvedProfiles.diagonal_witness supplies an explicit
upper bound on a successful diagonal offset. SolvedIdeal.scan searches
the offsets lazily, stopping at the first success and using the proved
upper bound only as its final fallback. witness_sound and witness_empty
prove both outcomes of that concrete function.

The arithmetic template has one natural-number coordinate per block.
For a square block its value is an increment above the positive base
run length. Binary-block coordinates are ignored by execution and
recorded as zero by witness recovery. request and emit convert these
vectors to the established arithmetic models. recover_spec proves
both box membership and exact program reconstruction.

For every template with positive base square counts and base cost at least
the excess, minimal_basis_correct proves that the computed finite list:

1. Contains only minimal points satisfying the at-or-below-target predicate.
2. Dominates every point satisfying that predicate in the entire unbounded
   increment domain.

hit_upward and basis_membership_iff explicitly prove that membership in the
upward closure of the computed basis is equivalent to the arithmetic
predicate. exact_solution_in_basis proves that every canonical exact solution
occurs in the basis. Canonical means that the bookkeeping coordinates of
binary blocks are zero, as they are in the original square-run parameter
space. canonical_cost_injective proves the necessary equality of parameter
vectors from ordered coordinates and equal primitive costs.

The safe-cutoff function is also computable. exact_cost_unchanged proves
that a covered exact-target program must have the same primitive cost as
its covering basis program: a positive cost increase would make its value
strictly less than the target. This handles ignored binary coordinates
without treating an irrelevant coordinate change as an extra instruction.
exact_below_cutoff proves that every exact-target program in the domain
has target index strictly below the computed cutoff.

The compiled Lean reference algorithm is compared with Python on 1,551
basis/cutoff cases. They cover every admissible lower corner generated for
controls of at most three blocks at excesses 0–3, plus larger shared
examples, nontrivial lower corners, and finite/mixed/unbounded boxes.
The compared lists contain 1,350 minimal points in total and have maximum
cutoff 5. This checker runs compiled Lean functions and compares their
outputs; it is execution evidence, not a kernel-evaluated finite equality
proof. Universal correctness and termination come from the formal theorems.

The reference recursion can revisit overlapping slices. Python retains
coordinate minimization and global box reuse; no universal refinement proof
equating that optimized implementation with the Lean function is claimed.

## Finite cover and universal assembly

UniversalCutoff closes those assembly steps with the following checked chain:

| Step | Formal declarations |
|---|---|
| Exhaustive finite integers and finite words | mem_upto, mem_words |
| Clip every run to the finite range [1,C+1] | clip, clip_length, clip_positive |
| Exact reconstruction by nonnegative increments | clip_reconstruct |
| Clipped base retains enough cost for every excess at most C | clip_cost_alternative, clip_admissible |
| Every bounded marked program belongs to the enumeration | clip_alphabet, clip_enumerated |
| Sound guarded leaf cutoff | template_cutoff_correct |
| Every leaf bound is below the finite aggregate | maximum_contains, portfolio_contains |
| Every bounded-control exact target lies below that aggregate | bounded_code_index |
| Complete coverage of increasing chains | effective_chain_bound, using mersenne_encoding |
| Transfer to arbitrary AM programs | effective_program_bound, using normalize |
| Computable additive-gap threshold and nonvacuity | effective_additive_gap, effective_minima |

For C, the construction sets M=12C+13 and enumerates all cell words of length
at most M, with saved addresses at most M and positive base run counts at
most C+1. The existing marked encoder proves that every relevant increasing
chain has a code inside those bounds. The enumeration deliberately includes
additional controls interpreted by the stated extended-history semantics.
Their cutoffs may enlarge the aggregate; they cannot remove a legal witness.

If no run is clipped, the original cost is preserved. If some run is clipped,
the base still contains C+1 squarings from that run alone. Thus every program
of cost at least its excess is reconstructed above an admissible finite base.
This avoids assuming a complete candidate menu or an unproved bound on the
actual run lengths.

templateCutoff returns an optional natural number: invalid bases or bases whose
target index would be negative return none, while a valid domain with no exact
solutions may return some 0. portfolio uses zero only as a neutral aggregate
value for absent leaves. Coverage proves that every relevant program has a
present, certified leaf. threshold takes the maximum of the aggregate and 1,
so the n=0 boundary is explicitly excluded from the final eventual statement.

The definitions use no noncomputable choice to select the threshold. Their
termination follows from finite enumeration and the proved basis recursion.
The proof may use the standard classical axioms listed in the audit; those
are not unspecified computational or arithmetic oracles.

## Component verification and practical limits

The new [component checker](../../checks/verify_universal_formalization.py)
kernel-checks 10,640 clipping and primitive-cost assertions, including run
counts of 10^100 and zero-count invalid inputs. It compares six finite
aggregates against an independent Python enumeration and checks six guarded
leaf cases, distinguishing absent bounds from valid zero cutoffs.

The six (C,M) fixtures are (0,0), (0,1), (1,1), (0,2), (1,2), (2,2).
Their enumerations contain 1, 11, 13, 463, 601 and 757 templates, and their
aggregates are respectively 1, 2, 3, 3, 5 and 7. These M values are separately
chosen component-test bounds. They are not the universal M=12C+13, so these
numbers are not evaluations of threshold C.

The universal function has not been numerically evaluated. Its exhaustive
enumeration can be extremely large, and no useful complexity bound,
closed-form growth rate or practical threshold is claimed. The optimized
Python implementation has finite comparison evidence, not a universal
formal refinement proof. Polynomial equivalence between AM and signed
program lengths remains a separate, unresolved question in this work.
