# Effective cutoffs for square-run arithmetic controls

**Status: the stated main claims now have complete Lean formalizations.**
The written presentation retains proof-draft status pending independent
review and novelty assessment. The checked construction includes ideal
intersection, complete bases, exact-solution inclusion, per-domain cutoffs,
finite coverage and a concrete computable universal threshold. See the
[statement correspondence](FORMALIZATION.md).

## 1. Question and scope

The [additive subtraction-gap theorem](../subtraction-gap/PROOF.md) proves that
only finitely many indices n satisfy

    τ₊(2^(2^n)−1) ≤ n+C

for any fixed C. Its finite-control/Dickson argument does not itself compute
the final exceptional index. Here we supply an effective extension with
a fully checked reference algorithm.

A **control** is a finite list starting from the saved value 1. Each block
either adds or multiplies two earlier saved values, or squares one earlier
value a positive number g_i of times. Every block saves its result; the last
result is the output E(g). The empty control outputs 1. With p binary blocks,

    r(g) = p + Σ g_i.

Earlier values may be reused. Values need not increase, and unused writes
still count. There is no bound on integer magnitude or storage. Subtraction,
division, zero-valued inputs and negative values are outside this model.

Fix a nonnegative excess j and a positive lower corner l with r(l)≥j.
The target and upward set are

    T(g) = 2^(2^(r(g)−j))−1,
    U = {g≥l : E(g)≤T(g)}.

**Theorem.** There is a terminating exact algorithm to compute the finite
minimal basis of U. It also decides whether U meets any box with lower corner
l and coordinate upper bounds in the natural numbers or infinity.
Every exact solution E(g)=T(g) belongs to that basis.

Consequently one can compute all exact solutions of a fixed control/excess
family and an index cutoff beyond which that family has no exact solution.
The reference implementation returns a safe cutoff from the basis without
having to filter it for exact equality.

**Corollary.** There is a computable function F(C) such that, for every
nonnegative C and every n≥F(C),

    τ₊(2^(2^n)−1) > n+C.

This is computability, with no useful complexity bound or closed-form rate
claimed. We have not computed F(C) by enumerating all controls. The finite
experiments below concern explicitly bounded control sizes.

## 2. Prior work and the specific extension

The general passage from ideal-intersection decisions to a computable
upward basis is the **Valk–Jantzen theorem**, not a new basis theorem here.
Aristote's 2025 paper states the original result as Theorem 1 and develops
an active-learning interpretation and extensions. We use ordinary tuples,
not its word/automaton generalization.
[Aristote, CALCO 2025](https://doi.org/10.4230/LIPIcs.CALCO.2025.16);
[Valk and Jantzen, 1985](https://doi.org/10.1007/BF00289715).

The specific proposed contribution here is an exact ideal-intersection
oracle for positive arithmetic square-run controls, using integer
exponential profiles and their leading coefficient. It supplies the
missing arithmetic input to that established basis machinery.

Altman's low-defect polynomial truncation motivates removing whole
parameter regions rather than waiting for isolated witnesses. His model
counts occurrences of 1 in expressions, unlike our reusable instruction
cost; none of his complexity theorems is transferred between the models.
The stability/self-similarity paper's version 6 is dated 17 October 2025.
[Altman, 2016](https://arxiv.org/abs/1603.06122);
[Altman and Arias de Reyna, v6](https://arxiv.org/abs/2111.00671v6).

Controlled descending-chain results require additional hypotheses before
their complexity bounds apply. We do not claim such hypotheses for this
algorithm. [Schmitz and Schütze, ICALP 2024](https://doi.org/10.4230/LIPIcs.ICALP.2024.153).
These sources were checked on 27 November 2026; this is not a priority claim.

## 3. Upward closure and minimal exact solutions

The already proved [control domination theorem](../../lean/ControlInflation.lean)
gives, for g≤h and q=Σ(h_i−g_i),

    E(h) ≤ E(g)^(2^q).

If g∈U and h≥g with h≠g, then q≥1 and

    E(h) ≤ T(g)^(2^q) < T(h).

The last strict inequality follows from (A−1)^k<A^k−1 for A≥2, k≥2.
Thus U is upward closed and every strict extension of one of its points
is strictly below its target. An exact solution cannot have a distinct
predecessor in U, so it is minimal. Conversely, a minimal point need not
be an exact solution.

## 4. A diagonal profile for an entire ideal

Consider a box I=[l,u], allowing u_i=∞. Fix finite coordinates at u_i;
keep each infinite coordinate initially at l_i. Call this anchor a.
Let J be the infinite coordinates, and d=|J|. The diagonal a(t) increases
each coordinate in J by t. It is cofinal in I: every point of I is
coordinatewise below some a(t).

For d=0, I has greatest point a and I meets U exactly when a∈U. Suppose
d>0, set x=2^t and n₀=r(a)−j, and define

    V = 2^(2^n₀).

Since r(a(t))=r(a)+dt,

    T(a(t))+1 = V^(x^d).

We construct a finite coefficient vector of positive integers
(B₀,…,B_d), with missing entries interpreted as 1, such that

    B_d^(x^d) ≤ E(a(t)) ≤ ∏_{e=0}^d B_e^(x^e).                 (1)

The two sides use the same leading coefficient B_d. In particular, d
counts **all** free runs, even unused runs, not just the degree of the
nonconstant output profile.

### Profile recurrence

A vector (b₀,…,b_k) represents the upper monomial ∏b_e^(x^e).
Pad vectors with 1 and remove trailing 1s after each operation.

| Operation | Resulting coefficient bases |
|---|---|
| Initial 1 | (1) |
| Addition of two constant profiles | Their exact constant sum |
| Any other addition | Componentwise maximum, with coefficient zero multiplied by 2 |
| Multiplication | Componentwise product |
| Fixed run of g squares | Raise every base to 2^g |
| Free run of g+t squares | Raise every base to 2^g, then prepend 1 |

The upper bound follows by induction. The only approximation is addition:
each operand's upper monomial is at most the componentwise-maximum
monomial, so their sum is at most twice it.

For the lower bound, strengthen the induction as follows. After a prefix
with k processed free runs, every saved value has profile degree at most
k and is bounded below by its coefficient at degree k raised to x^k.
At k=0 all profiles are exact constants. For k>0 an addition's top
coefficient is the maximum of the operand coefficients; one summand
already supplies that lower bound. Multiplication multiplies the two
lower bounds. A fixed square run raises them to its fixed power.
A new free square run shifts the new value's profile and lower bound
from degree k to k+1. Earlier saved values now have coefficient 1 at
degree k+1, and are positive, so their new lower bounds remain valid.
This proves (1) for the entire saved history, including arbitrary reuse.
If both profiles in a later addition are constant, their top coefficient
at k>0 is simply 1, so the exact constant-sum shortcut also preserves
this invariant.

The implementation omits materialization of unused output ancestors.
Their writes and free-run counts remain in the cost and dimension.
All block references are validated even when their values are unused.

## 5. Deciding ideal intersection

Write B=B_d.

If B≥V, equation (1) gives E(a(t))≥V^(x^d)>T(a(t)) at every diagonal point.
If any point of I belonged to U, cofinality and upward closure would put
a diagonal point in U, a contradiction. Therefore I∩U is empty.

If B<V, let S=∏_{e<d}B_e. Since x≥1 and e≤d−1,

    E(a(t)) ≤ B^(x^d) S^(x^(d−1))
             = (B^x S)^(x^(d−1)).                            (2)

Choose a power of two x≥BS. Because V≥B+1 and B≥1, the first two
binomial terms yield

    V^x ≥ (B+1)^x ≥ B^x + x B^(x−1)
        = B^(x−1)(B+x) > B^x S.

Combining this with (2) gives E(a(t))<V^(x^d), so the positive integer
endpoint is at most T(a(t)). This explicitly supplies a witness in I∩U.
All coefficients are computable integers; therefore the oracle terminates
with unrestricted exact arithmetic.

The program chooses such a power without building BS by setting
t=Σ_{e≤d}bit_length(B_e), which gives 2^t>BS. A faster alternative uses
integer ceiling logarithms b_e=bit_length(B_e−1). Put A=2^n₀. If
Δ=A−b_d>0, any 2^t Δ>Σ_{e<d}b_e proves the same strict domination.
The program takes t=bit_length(floor(Σ_{e<d}b_e/Δ)). If A already exceeds
Σb_e, t=0 suffices; that comparison is made by bit lengths when n₀ is huge.
If Δ≤0 while B<V, the integer-ratio witness handles the unresolved case.

No floating-point logarithm, numerical limit or approximate equality is
used. The finite exact anchor is checked first as an optimization.

## 6. Extracting a complete basis and cutoff

Start with the single residual box [l,u]. Query a residual box. Delete it
if empty. Otherwise minimize the returned U witness one coordinate at a
time, using binary membership searches. Once a coordinate is minimal,
decreasing other coordinates cannot turn its rejected predecessor into a
member: U is upward closed. The final point p is therefore minimal in U
relative to the common lower corner.

Subtract its upward orthant from every residual box. A box already
disjoint from that orthant is unchanged. Otherwise its complement is
the union, over coordinates with p_i>l_i, of the same box with upper
bound i replaced by min(u_i,p_i−1). Duplicate and contained boxes may
be discarded. This maintains exactly the unexplored region.

Every new minimal point is distinct from, and incomparable with, the
earlier ones. Dickson's lemma permits only finitely many such points.
Between additions there are only finitely many boxes to delete.
Thus the procedure terminates with a complete basis M, as in the
Valk–Jantzen construction.

The formal reference algorithm uses the same box-complement identity in a
recursive form. It selects any oracle witness p inside a box, recursively
solves each coordinate slice x_i<p_i, and prunes dominated points afterward.
Each slice replaces one upper bound with p_i−1. Because p belongs to the
parent box, this strictly lowers the lexicographic pair

    (number of infinite upper bounds, sum of finite upper bounds).

An infinite bound becoming finite lowers the first component. Otherwise
the first is unchanged and a finite bound decreases. This gives a concrete
well-founded recursion over natural-number pairs, including zero-dimensional
boxes and zero-valued coordinates. Overlapping slices may repeat work; final
pruning removes duplicate and dominated generators. The generic correctness
theorem is instantiated with the actual arithmetic witness function, so no
external witness oracle is assumed in the arithmetic conclusion. The Python
implementation retains its more efficient coordinate minimization and global
residual-box reuse. The formal reference covers the same unbounded domains;
a universal refinement proof for Python is not claimed.

All exact solutions are in M. A safe cutoff is 0 if M is empty, and
otherwise

    1 + max_{g∈M}(r(g)−j).

This cutoff can exceed the true final exact-solution index because some
minimal points are strictly below their target.

To cover all positive run vectors with r(g)≥j, use the all-one lower
corner if its cost is at least j. Otherwise, when there are d>0 runs,
use every positive composition of j−p into d parts. Every admissible
vector dominates one such composition. With no runs and p<j the domain
is empty. Take the maximum completed cutoff over this finite cover.

The resource-bounded API returns resource_limit and cutoff=None when
an exact query, integer or residual-region budget is exhausted. It
preserves the completed minima and unresolved boxes. Budget exhaustion
is never an emptiness certificate. These budgets are accounting limits,
not a guarantee against every platform-level memory failure.

## 7. Universal computability corollary

For n≥1, a program for N_n=2^(2^n)−1 needs at least n writes.
Normalize any AM witness of length at most n+C to an increasing chain
without increasing length. The [checked nonsquare bound](../../lean/NonsquareBound.lean)
gives p≤4C+4. The [complete marked encoding](../../lean/MarkedEncoding.lean)
has at most 3p+1≤12C+13 blocks, preserves the endpoint and exact cost,
and supplies legal earlier-mark references.

There are finitely many such controls and excesses j=r−n in [0,C].
The formal construction uses the following finite cover of their run
parameters. Replace every positive run g_i by

    l_i = min(g_i,C+1).

If no run changes, the base cost is the original cost and is at least j.
If a run changes, the base includes at least C+1 writes from that run
alone, so its cost is again at least j. Thus every admissible program
belongs to one of the finitely many domains with positive bases in
[1,C+1]. Increasing those base runs by g_i−l_i reconstructs the original
program and its exact primitive cost.

Set M=12C+13. Enumerate all words of length at most M over the cells

    add(a,b), multiply(a,b)     with 0≤a,b≤M,
    square_run(a,l)            with 0≤a≤M and 1≤l≤C+1.

This is a finite superset of the marked controls. The formal marked
interpreter extends out-of-range saved addresses with copies of 1, and
the arithmetic cutoff theorem also applies to that explicitly stated
semantics. Every legal encoding is included; the extra controls can only
enlarge the maximum cutoff.

For each cell word and j∈[0,C], compute its cutoff when the base cost is
at least j. Inadmissible inputs return no leaf bound, rather than an
emptiness claim. Let P(C) be the maximum of the returned cutoffs and set

    F(C) = max(1,P(C)).

Every hypothetical witness with n≥F(C) would belong to one of these
domains, contradicting its proved cutoff. Normalization transfers the
conclusion to arbitrary AM programs. All steps are present in
[UniversalCutoff](../../lean/UniversalCutoff.lean), including finite-list
membership, clipping, exact reconstruction and the final program theorem.

The function F is a computable Lean definition, not a choice of an
unspecified sufficiently large index. Its enumeration can be immense.
No useful complexity bound or practical numerical evaluation of F is
claimed.

For an additive gap of at least K over signed programs, combine the
cutoff for C=K+2 with the known n+2-write subtraction construction.
This still gives no polynomial or superpolynomial separation.

## 8. Reproducible examples and evidence

Two independently replayed families exercise multiple incomparable minima:

| Endpoint E(g₁,g₂) | Binary writes p | Excess j | Minimal U points | Safe cutoff |
|---|---:|---:|---|---:|
| 2^(2^g₁) · 2^(2^g₂) | 2 | 3 | (2,3), (3,2) | 5 |
| 3(2^(2^g₁)+1)(2^(2^g₂)+1) | 6 | 6 | (1,2), (2,1) | 4 |

The first has no exact Mersenne solution because its output is a positive
power of two greater than one. In the second both minima output 255 at
target index 3. These are template cutoffs, not universal AM bounds.

The [small-control census](../../checks/verify_control_cutoffs.py) enumerates
all 388 controls of at most three blocks, treating + and × operands as
unordered. Each square block may read any earlier mark. For excesses
0,1,2,3, all **1,552 families** complete. Independent expanded-instruction
replay checks **8,394** valid parameter points with each run in [1,4],
including 204 exact hits. The maximum reported template cutoff is 4.
A digest covers every canonical control/excess/basis record; these
numbers are reproduced by the [stored certificate](../../checks/expected/control-cutoffs.json).

Additional tests cover every free-run subset of all at-most-one-small-step
increasing chains through 64, randomized controls, every finite box in
the two examples, integer-ratio fallback, empty controls, repeated operands,
unused huge runs, immutable one-shot inputs, and partial resource stops.
The finite checks test the implementation; they are not proofs of the
unrestricted profile or basis theorems.

    python -m scripts.verify effective-control-cutoffs
    python -m checks.verify_control_cutoffs
    python -m scripts.check_certificates
    python -m scripts.check_formalization

The initial [EffectiveCutoffs inequalities](../../lean/EffectiveCutoffs.lean) are now
connected to [complete profile extraction](../../lean/DiagonalProfiles.lean) and
the [full ideal oracle](../../lean/IdealOracle.lean). The final decision theorem
takes no supplied profile bounds or oracle hypothesis. It covers arbitrary
positive lower bounds and both finite and unbounded upper bounds. The
[model-comparison checker](../../checks/verify_profile_formalization.py) additionally
checks 779 profiles, 1,558 endpoints and 3,073 decisions between Python and Lean.
Those finite checks support representation agreement; the unrestricted oracle
result follows from the formal proof. The [reference basis algorithm](../../lean/FiniteBasis.lean) and its
[arithmetic instantiation and cutoff](../../lean/ArithmeticBasis.lean) now
complete the proof for every admissible lower-corner domain. Compiled Lean
execution matches Python on 1,551 basis/cutoff cases, with 1,350 minimal
points counted across cases and maximum compared cutoff 5. This is finite
execution evidence, separate from the universal formal theorems. The
[universal construction](../../lean/UniversalCutoff.lean) now completes
the finite cover and threshold assembly. Its component checker verifies
10,640 clipping/cost assertions, six small finite aggregates and six guard
cases. The aggregates deliberately use independently selected block bounds
at most two; they are not values of the universal F. Universal refinement
of the optimized Python implementation remains outside the formalization.
See the [formal scope](FORMALIZATION.md).
