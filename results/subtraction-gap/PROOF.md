# An unbounded additive advantage for subtraction

**Status: the main theorem has an end-to-end Lean proof.** Independent mathematical review of the presentation and publication priority remains pending. The [formal statement correspondence](FORMALIZATION.md) identifies the exact models, quantifiers and coverage.

Let τ₊(n) be the minimum number of +,× instructions computing a positive integer n from 1, allowing reuse of previous values. Let τ(n) allow subtraction as well. For

    Aₙ = 2^(2ⁿ),    Nₙ = Aₙ−1,

we derive

    τ₊(Nₙ) − n → ∞,
    τ₊(Nₙ) − τ(Nₙ) → ∞.

The second conclusion follows from the explicit subtraction construction τ(Nₙ)≤n+2. Saranurak and Jindal study this same family, prove an eventual one-instruction advantage, and ask for a growing additive gap in their conclusion. The argument below addresses that additive question. It provides no quantitative growth rate for the gap and leaves their polynomial-equivalence question open. The manuscript and its correspondence to the literature await independent review. [Original paper, §3 and conclusion](https://arxiv.org/pdf/1212.2549)

## 1. A bounded number of nonsquares

Any positive AM program can be normalized without increasing its length. Keep the distinct computed values no greater than its endpoint. Every value beyond 1 has a recipe from strictly smaller values after bypassing identity writes. Constructing these values in increasing order preserves operand availability, reaches the endpoint and uses at most one write per original computed value. AMNormalization proves this for arbitrary programs, including repeated and decreasing writes.

For an increasing chain 1=a₀<a₁<…<aᵣ, call a step a canonical square when aᵢ=aᵢ₋₁². The value 2→4 is normalized as a square even when its written recipe was 2+2. Let p be the number of other steps. Write λ(aᵣ)=L, with

    2^(2^(L−1)) ≤ aᵣ < 2^(2^L),

and put s=r−L. We only need a bound on p depending on s.

For i≥1 let uᵢ=log₂(aᵢ)/2^(i−1). Since a₁=2 and every subsequent value is at most its predecessor squared, u is non-increasing and starts at 1. Also uᵣ≥2^(−s). At a nonsquare position t≥3,

    aₜ ≤ aₜ₋₁ aₜ₋₂,
    uₜ ≤ uₜ₋₁/2 + uₜ₋₂/4.

The product bound holds because every nonsquare product has an operand at most aₜ₋₂, and every addition is at most 2aₜ₋₁≤aₜ₋₁aₜ₋₂.

After the initial write 1→2, pair successive nonsquare positions j<k. Then k≥3 and k−2≥j−1, so the second member has normalized value at most (3/4)uⱼ₋₁. Intervening squares and any unpaired step cannot increase u. Thus

    uᵣ ≤ (3/4)^floor((p−1)/2).

If p≥6s+3, the right side is at most (3/4)(27/64)^s<2^(−s), a contradiction. Consequently **p≤6s+2**. This elementary coarse bound suffices below. The sharper published nonsquare bound is consistent with it. [Tarek, Bahig and Anwar, Corollary 3.1](https://doi.org/10.3934/Math.2026667)

### A fully checked integer alternative

The following bound supplies the needed finiteness without logarithms:

    p ≤ 4s+4.

It is a coarse consequence of the Fibonacci envelope technique in the cited AM-chain literature. After the mandatory first write 2=1+1, let b=p−1 be the remaining canonical nonsquare count and let d be the square count. Induction on the chain gives

    aᵣ ≤ 2^(2^d F_{b+2}),
    aᵣ₋₁ ≤ 2^(2^d F_{b+1}),

where F₀=0 and F₁=1. The initial virtual pair is (2,2), an upper bound on the actual pair (2,1). A canonical square squares the first bound; its former head fits the second bound since F_{b+2}≤2F_{b+1}. A nonsquare is bounded by the product of the two current bounds: a noncanonical product must use an earlier operand, and an addition is at most twice the head while the virtual second bound is at least two. The Fibonacci recurrence then advances b.

One has F_{b+6}≤8F_{b+2}, and the four initial cases give

    F_{b+2} ≤ 2^(b−floor(b/4)).

Consequently aᵣ≤2^(2^(d+b−floor(b/4))). Comparing with the growth-level lower bound 2^(2^(L−1)) and using r=1+b+d≤L+s yields floor(b/4)≤s, hence p=b+1≤4s+4.

The Lean development proves the first write, existence of the canonical step count for every increasing chain, the envelope, the Fibonacci estimate and the final count bound. The direct theorem `mersenne_nonsquare_bound` applies to a chain ending at 2^(2^n)−1 with r≤n+C, giving p≤4C+4. It uses only integer powers and inequalities. [Formal proof](../../lean/NonsquareBound.lean) · [Independent finite checker](../../checks/verify_nonsquare_bound.py).

## 2. Finite controls and their square parameters

Mark the initial value, final value, every nonsquare result and both operands of every nonsquare. There are at most 3p+2 distinct marks. Between consecutive marks, every unmarked instruction is a square.

A marked nonsquare must immediately follow the preceding mark. Otherwise its predecessor would be an unmarked square m=b² with b≥2. If the nonsquare did not read m, its product would be at most b²=m and its sum at most 2b≤m, contradicting strict increase. Reading m would itself make that predecessor a mark.

Therefore each transition between marks is either a nonsquare with two references to earlier marks, or a positive-length run of squares starting at the preceding mark. For bounded p there are finitely many such controls. Only the square-run lengths vary. If a control has p nonsquares and square lengths g₁,…,g_d, its instruction count is

    r = p + Σgᵢ.

With p nonsquares there are at most 3p+1 block transitions and at most 2p+1 square-run parameters. There are finitely many operation labels and references to earlier marks at each of these boundedly many positions. This representation retains every nonsquare operand even when it lies inside a long run. The implemented encoder reconstructs the full numerical chain, with canonical normalization of 2→4. The Lean module ChainCoverage now proves that a nonsquare predecessor is marked, that a nonsquare boundary is adjacent to its preceding mark, and that a square boundary is exactly the iterated square of that mark. It formalizes these local coverage steps for every chain satisfying its explicit increasing-AM definition. [Encoder and decoder](../../solved/square_controls.py)

### Complete marked-code extraction

`MarkedEncoding.complete_encoding` now proves the encoding's existence for every increasing AM chain. The proof scans original writes in order, accumulating an unmarked square run until the next marked value. A nonsquare's predecessor is marked, so it has no pending squares; its operands have already been saved. Every emitted block references available saved values, and the saved-history invariant preserves every earlier marked value.

For the size bound, the proof begins with a list containing the final index and three indices for every nonsquare: its result and two operands. Duplicates are permitted. Each emitted block removes one occurrence of its own index. All future marked indices survive because they differ from the removed index. This proves the bound 3p+1 without assuming a correct sorting or deduplication procedure.

At the final mark, the pending run is empty. The emitted program has exactly r arithmetic writes, reaches the original endpoint, has at most 3p+1 blocks, and uses bounded operand addresses. The direct `mersenne_encoding` corollary gives at most 12C+13 blocks for the near-linear Mersenne budget. This is a formally checked existence proof; it does not assert that the Python encoder's implementation has been verified. [Complete extraction theorem](../../lean/MarkedEncoding.lean).

## 3. Domination when square parameters increase

Fix one control. Increase one run length by one while keeping every other parameter fixed. At the changed mark the new saved value is the square of its old value. Previously saved values remain unchanged and are bounded by their own squares. Thereafter multiplication preserves the coordinatewise squared bound. Addition preserves it because

    x²+y² ≤ (x+y)².

An unchanged square run preserves it too. Consequently the new endpoint is at most the old endpoint squared, while the written length increases by one. This is an algebraic assertion about positive expressions, valid even if an intermediate parameter choice loses the strictly increasing order required for a canonical chain.

Iterating the comparison gives the following. If g≤h coordinatewise and their length difference is q=Σ(hᵢ−gᵢ), then

    endpoint(h) ≤ endpoint(g)^(2^q).

The earlier Lean lemma one_extra_square checks a single insertion. The new ControlInflation module proves the general comparison directly, including saved-history reads and exact write counts. Its `comparable_domination` theorem takes two programs with the same erased arithmetic control and coordinatewise ordered run lengths, then uses q=cost(new)−cost(old). Programs can have several enlarged runs at once. Additions obey the iterated-square inequality; multiplication commutes with common iterated squaring. [General comparison](../../lean/ControlInflation.lean).

## 4. The contradiction

Fix an arbitrary integer C≥0. Suppose infinitely many n admit an AM chain for Nₙ of length r≤n+C. Since Nₙ exceeds the maximum attainable in n instructions, r≥n+1. Also λ(Nₙ)=n, so s≤C and the checked integer bound gives p≤4C+4. Choose a witnessing chain for each n.

There are finitely many values of r−n and finitely many controls. On an infinite subsequence both the excess j=r−n and the control are fixed. Sort this subsequence by n. Dickson's lemma supplies two indices n<m whose square-run vectors are coordinatewise ordered. Their length difference is exactly m−n, so the domination inequality gives

    Nₘ ≤ Nₙ^(2^(m−n)).

But Aₘ=Aₙ^(2^(m−n)), and for any integer A≥2 and exponent q≥2,

    A^q−1 > (A−1)^q.

Hence Nₘ>Nₙ^(2^(m−n)), the contradiction. For every C, only finitely many n therefore have τ₊(Nₙ)≤n+C, proving τ₊(Nₙ)−n→∞. The signed program writes 2, squares n times, and subtracts the saved 1, using n+2 instructions. Hence τ₊(Nₙ)−τ(Nₙ)→∞ as well.

The formal proof assembles this argument without assuming an encoding or domination property. BoundedControls packs operation tags, saved-operand addresses and their bounded complements alongside run lengths and length excess. Dickson comparison forces identical control and excess, with coordinatewise longer runs. The checked `mersenne_program_antichain` theorem then supplies the contradiction.

AMNormalization transfers the lower bound from increasing chains to arbitrary AM programs without increasing cost. AdditiveSeparation combines it with the integer signed construction and proves existence and uniqueness of the minimum costs. The main conclusion is checked end to end; the [statement correspondence](FORMALIZATION.md) records its exact scope.

## 5. Other explicit families and bounded positive storage

The same finite-control argument applies to any integer sequence bₙ with λ(bₙ)≥n−O(1) and bₙ₊₁>bₙ². A hypothetical bound τ₊(bₙ)≤n+C again yields bounded s, finitely many excesses and controls, and the same contradictory pair.

For any fixed positive c, Aₙ−c meets these conditions for sufficiently large n because

    (Aₙ²−c)−(Aₙ−c)² = c(2Aₙ−c−1)>0.

It has a signed construction of length n+O_c(1). Another family is Aₙ−Aₙ₋d for any fixed lag d≥1. The old lower tower value is already available and one subtraction completes the target. The strict growth comparison follows from A²−B²>(A−B)² when A>B>0. These give additional unbounded additive separations.

The primary Mersenne-family separation also survives a cap equal to the target. Build B=2^(2^(n−1)), then B−1, B+1 and their product. This uses n+3 instructions, three registers, positive values throughout and no intermediate greater than Nₙ. The monotone lower bound was obtained with unrestricted storage, so it also lower-bounds any fixed-register AM machine. The infinite-family statement lets the cap grow with the instance.

Exact division has an analogous separation from +,× on the powers Aₙ/2. Their consecutive ratio gives bₙ₊₁=2bₙ², and their level is n. Keeping 2 while squaring and then dividing by it gives n+2 instructions. This conclusion compares exact division with the monotone AM model.

## 6. A constructive exclusion rule

Fix a marked control and a nonnegative integer excess j. A parameter vector g with positive square-run lengths has written length r(g). Its associated target is

    T(g) = 2^(2^(r(g)−j)) − 1,

where r(g)≥j. Suppose a checked base description has endpoint E(g)≤T(g). For every coordinatewise extension h≥g with h≠g, put q=Σ(hᵢ−gᵢ)>0. The fixed control makes r(h)−r(g)=q. The comparison from §3 gives

    E(h) ≤ E(g)^(2^q) ≤ T(g)^(2^q) < T(h).

Thus **no strict extension can represent its associated tower-minus-one target at excess j**. If the base is strictly below its target, the base itself is excluded too. If it equals the target, retain that solution and exclude only strict extensions. This is a certificate for an entire upward region of parameters, including vectors with arbitrarily large coordinates. It does not exclude incomparable vectors, other controls or another excess.

For example the chain 1,2,4,5,10,15 has length five, excess three, and endpoint N₂=15. Its marked control has one square run of length one. Increasing that run to length two produces 1,2,4,16,17,34,51, with length six and endpoint 51<N₃=255. Every further extension of the same run is excluded at excess three by the certificate, without constructing its endpoint.

The implementation evaluates the base exactly and verifies membership of later parameter vectors by coordinate comparisons. It compares a base integer with 2^(2^n)−1 by bit length and the all-ones binary test, without materializing the target tower. A failed certificate condition supplies no exclusion. [Executable certificate](../../solved/square_exclusions.py) · [Independent finite checks](../../tests/test_square_exclusions.py). The Lean lemma exclusion_by_growth checks the strict propagation from a supplied domination inequality.

## 7. Effectivity of the original argument and follow-up

Dickson's lemma proves the finiteness used in §4. Known quantitative bounds for bad sequences additionally require a control function restricting coordinate growth. The later theory of strongly monotone descending chains supplies sharper bounds under further hypotheses. Neither condition has been established for the witnesses here. In particular, the index of the next exceptional tower exponent could be very large compared with its position in a list of exceptions. We therefore do not claim an effective cutoff or a numerical rate for the additive gap. [Figueira et al., controlled Dickson bounds](https://arxiv.org/abs/1007.2989) · [Schmitz and Schütze, ICALP 2024](https://doi.org/10.4230/LIPIcs.ICALP.2024.153).

The exclusion certificate is useful even without such a cutoff: any verified base removes all its strict coordinate extensions at the same control and excess. A complete search must still account for every control and every remaining incomparable region. A new representation or arithmetic argument is needed to make that coverage effective. The separate [effective-control-cutoff manuscript](../effective-control-cutoffs/PROOF.md) now proposes such an extension: integer diagonal profiles decide ideal intersection, enabling a Valk–Jantzen basis computation. Its computable-threshold corollary now has its own complete Lean formalization; independent mathematical review and priority assessment remain pending. No practical universal threshold has been computed.

## Verification scope

The finite-control encoder, reconstruction and one-square inflation are tested on all at-most-two-small-step chains through 10^18 and further small cases. Additional tests compare exclusion certificates against exact small endpoints, preserve an exact base solution, reject incomparable parameters, and test membership with an exponent parameter of 10^100 without expanding that candidate.

Lean checks the main conclusion end to end. The final theorem states that for every C there is a threshold after which every minimum AM cost a and minimum integer signed-program cost b for Nₙ satisfy b+C<a. Minimum costs are proved to exist and be unique. The signed model allows zero and negative intermediates, and the normalization theorem covers AM programs whose outputs are not ordered or distinct.

The complete dependency chain includes the integer nonsquare bound, full marked-code extraction, exact-cost control domination, finite-dimensional comparison, arbitrary-program normalization and the explicit signed construction. No ordinal-defect conjecture, finite census or external unproved theorem is assumed. [Statement and model audit](FORMALIZATION.md) · [Final formal theorem](../../lean/AdditiveSeparation.lean).

Independent Python checks cover 812 distinct sampled AM programs, including decreasing writes, identities, duplicates and unused overshoots; signed traces with zero and negative values; and explicit tower witnesses. Two exact enumerators check each listed finite AM minimum. These checks are model-conformance evidence, not the proof of the asymptotic result. [Model checker](../../checks/verify_additive_separation.py) · [Stored checks](../../checks/expected/additive-separation-models.json).

The formal theorem in this entry supplies no quantitative gap-growth rate or computed threshold; the effective extension is tracked separately. It is an additive separation, compatible with the known upper bound τ₊(Nₙ)≤2n from the original paper; it does not resolve polynomial equivalence. The other families, finite-cap/register variants and exact-division consequences above remain outside the complete formalization. Independent mathematical review and publication-priority assessment are pending.
