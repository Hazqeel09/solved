# Directed recovery from monotone polynomial intervals

**Status: research proof draft; independent mathematical review pending.** Lean proves the abstract signed-transport uniqueness theorem. The polynomial gap certificates, reconstruction algorithm and bit-complexity analysis below have written proofs and differential tests, and are not formalized end to end.

## Model and prior work

For a finite nonempty set of variables, each xᵢ ranges over a nonempty positive integer interval [mᵢ,Mᵢ]. Each observation e=(i,j) specifies

    Lₑ ≤ Fₑ(xᵢ,xⱼ) ≤ Uₑ,
    Fₑ(x,y) = Σ cₚq x^p y^q,

with nonnegative integer coefficients and exponents. Coefficients, exponents, domain bounds and observation bounds are binary encoded. Zero polynomials, loops and parallel observations are allowed. Negative coefficients and divisions are outside this representation.

Functional binary constraints and directed propagation are established ideas. The [1993 IJCAI paper](https://ijcai.org/proceedings/1993/32) develops directed root sets and reductions through functional constraints. [Ma et al.](https://jmlr.org/papers/volume21/19-359/19-359.pdf) study the non-bipartite criterion for real rank-one recovery. Our [narrow-product result](../narrow-products/PROOF.md) uses integer spacing and finite intervals. The present result combines one-sided spacing certificates, antitone cycle inversion and succinct polynomial arithmetic. No priority claim is made for functional propagation or cycle-based identifiability.

## 1. A directed functional certificate

Put wₑ=Uₑ−Lₑ. The smallest unit increment in y over the domain is

    Δᵧ = Fₑ(mᵢ,mⱼ+1) − Fₑ(mᵢ,mⱼ).

All coefficients are nonnegative, so this increment is nondecreasing in each input. If **Δᵧ>wₑ**, every fixed x permits at most one feasible y. Any two different integer y values differ by at least one unit, changing F by more than the entire observation interval. Create a directed arc i→j for this certificate. The reverse direction uses Δₓ and is checked independently.

For F(x,y)=xy, the arc i→j requires only wₑ<mᵢ. The old two-sided requirement imposed this in both directions. For F(x,y)=x+100y, any width below 100 certifies i→j even when the reverse direction is not functional.

The strict comparison is necessary for this local guarantee. For F(x,y)=100y and a fixed x, the interval [100,200] contains both y=1 and y=2 at width Δᵧ=100. The condition is sufficient, not necessary, for a particular constraint to be functional.

## 2. Exact antitone transports

For each certified arc i→j and source value a, define Tₑ(a) as the largest b∈[mⱼ,Mⱼ] with Fₑ(a,b)≤Uₑ. If there is no such b, set Tₑ(a)=mⱼ. Since F is nondecreasing in its first coordinate, Tₑ is non-increasing: it is an antitone map. For the abstract formal theorem, extend this map to all natural inputs by first clamping the source to its domain. This preserves order and agrees on every legal assignment.

Every feasible pair (a,b) has b=Tₑ(a). Indeed, Δᵧ>wₑ implies Fₑ(a,b+1)>Uₑ whenever b+1 is in the domain. Thus no larger candidate passes the upper bound. The definition is total and clamped, but a clamped candidate can violate the lower bound or even the upper bound. Every recovered observation is therefore checked explicitly.

A monotone binary search evaluates Tₑ in O(B) polynomial comparisons, where B bounds the bit lengths of the integer domains. If F is affine in its destination variable, F(a,b)=A(a)b+C(a), use the exact quotient floor((Uₑ−C(a))/A(a)), clamped to the destination interval. A certified direction has A(a)>0. This includes ordinary product transport and avoids a second binary search in that case.

## 3. Seeds, directed cycles and uniqueness

A seed is a variable fixed by its domain, or uniquely determined by a certified univariate observation. An observation independent of its source gives a constant transport and can supply a seed. A self-observation F(xᵢ,xᵢ) is treated as G(xᵢ)=Σcₚq xᵢ^(p+q); the diagonal increment can be stronger than either separate-coordinate increment. For example 3≤x²≤5 on [1,3] has the unique solution x=2, certified by diagonal gap three even though the separate increments of xy at (1,1) are only one.

**Uniqueness theorem.** Suppose every vertex is reachable along certified arcs from either a seed or a vertex lying on an odd directed closed walk. Then the full observation system has at most one assignment.

An odd composition of antitone transports is antitone. Any feasible value at the walk's starting vertex is a fixed point of that composition. An antitone map on an integer interval has at most one fixed point: if a<b were both fixed, antitonicity would give b≤a. Thus the walk fixes at most one root value. Directed functional propagation fixes at most one value at every reachable vertex. Seed values agree across any two feasible assignments, so the coverage condition proves the theorem, including disconnected systems.

More generally, allow individual transports to be monotone or antitone. A closed walk with an odd number of antitone arcs has the same property. The Lean theorem `unique_assignment` proves this signed version from explicit path coverage, transport equations, order hypotheses and seed equalities. [Formal source](../../lean/DirectedRecovery.lean). It does not assume or prove these hypotheses for arbitrary user-supplied functions.

## 4. Complete reconstruction on the covered class

Compute the functional graph and its strongly connected components. Propagate domain and univariate seeds. In each still-unassigned component, search the two parity copies of its directed graph for a path from (r,0) to (r,1). This yields an odd closed walk rooted at r, of length at most twice the component size minus one.

If an odd closed walk exists elsewhere in that strongly connected component, one exists at r: take paths to and from its base, and compare the closed walk with and without the odd excursion. Their lengths have opposite parity. Thus testing one root per component is sufficient.

For each resulting walk, compose the transports into H. The predicate H(a)≥a is monotone decreasing in a. Binary search for its largest satisfying argument. If it is not a fixed point, no feasible assignment exists. Otherwise propagate that root along all outgoing arcs. Conflicting assigned values or a violated fully determined observation prove infeasibility. Finally verify every observation before returning a complete tuple.

Under the coverage condition, this procedure returns the unique solution or proves infeasibility. Outside it, the implementation may still prove an immediate contradiction, but otherwise returns **undetermined** with the values forced by the available certificates. Undetermined does not mean feasible, nonunique or unsatisfiable. These are numerical recovery results; they supply no minimum-cost arithmetic program for constructing the recovered values.

## 5. Polynomial bit complexity with binary-encoded degrees

A direct evaluation of x^p can have exponentially many bits in the encoding length of p. The algorithm only needs comparisons with finite observation bounds, so it evaluates nonnegative expressions with saturation at K=Uₑ+1. For nonnegative additions and multiplications, saturating inputs and then the result gives exactly the saturated full result. Binary exponentiation therefore computes min(x^p,K) in O(log(p+1)) capped arithmetic operations.

The increment test must not subtract independently saturated powers. For Dₙ=(b+1)^n−b^n, maintain Pₙ=b^n, Qₙ=(b+1)^n and Dₙ. Binary exponentiation uses the positive identities

    D₂ₙ = Dₙ(Pₙ+Qₙ),
    D₂ₙ₊₁ = (b+1)D₂ₙ + P₂ₙ.

All three quantities can be saturated after each operation. Starting at P₀=Q₀=1 and D₀=0 proves the recurrence by induction. Multiplying each increment by its other monomial factors and summing gives the coordinate gap, capped at wₑ+1. Every intermediate has polynomially bounded bit length. The same reasoning validates saturated slope and offset evaluation for affine transports: if either exceeds Uₑ, every positive destination exceeds the observation; otherwise both are exact.

Strongly connected components and parity searches use O(V+E) graph work. Odd walks selected in distinct components have total length O(V). Their root searches use O(B) walk evaluations, and each general transport uses O(B) polynomial comparisons. Propagation and final checking add O(EB+E) comparisons. Thus O(VB²+EB+E) polynomial-evaluation or coefficient-evaluation calls suffice, plus gap computation. Since each call costs polynomial time in the binary input size, the covered class is decidable in polynomial bit complexity. This bound does not enumerate the values in an interval. Affine destination dependence removes the inner O(B) inversion cost for those arcs.

## 6. Examples and verification

Three one-way observations of xᵢ+100xⱼ on a directed triangle, each within one unit of the values generated by (5,7,11), recover that tuple over domains [1,100]. A noisy-product triangle recovering (101,107,109) can determine an additional factor 3 through a one-way product observation even when that factor's domain starts at 1. The old two-sided condition rejects that leaf edge.

Tests compare recovery with every assignment on 800 fixed-seed random small systems and check 1,200 capped polynomial evaluations and increments against full integer arithmetic. They also cover reversed non-symmetric edges, anchors, multiple components, parallel observations, loops, empty integer preimages, equality at the spacing boundary, an odd cycle away from the chosen root, and unsupported even components. Large cases use domains up to 10^18 and exponents as large as 10^100 without constructing their expanded powers.

[Implementation](../../solved/monotone_recovery.py) · [Tests](../../tests/test_monotone_recovery.py). The existing specialized product algorithm remains available. The generalized engine uses the same exact quotient principle for affine inversion; it incurs additional graph and polynomial bookkeeping.
