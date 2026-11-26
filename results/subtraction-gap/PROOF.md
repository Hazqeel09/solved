# An unbounded additive advantage for subtraction: proof draft

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

**Research proof draft.** Let τ₊(n) be the minimum number of +,× instructions computing a positive integer n from 1, allowing reuse of previous values. Let τ(n) allow subtraction as well. For

    Aₙ = 2^(2ⁿ),    Nₙ = Aₙ−1,

we derive

    τ₊(Nₙ) − n → ∞,
    τ₊(Nₙ) − τ(Nₙ) → ∞.

The second conclusion follows from the explicit subtraction construction τ(Nₙ)≤n+2. Saranurak and Jindal study this same family, prove an eventual one-instruction advantage, and ask for a growing additive gap in their conclusion. The argument below addresses that additive question. It provides no quantitative growth rate for the gap and leaves their polynomial-equivalence question open. The proof is awaiting independent mathematical review. [Original paper, §3 and conclusion](https://arxiv.org/pdf/1212.2549)

## 1. A bounded number of nonsquares

A shortest positive AM computation can be put in strictly increasing numerical order. Discard unused writes, remove multiplication by 1 and duplicate values, and sort the remaining nodes by value. Each useful addition or multiplication produces a result strictly greater than both inputs, so every dependency remains earlier in this order.

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

## 2. Finite controls and their square parameters

Mark the initial value, final value, every nonsquare result and both operands of every nonsquare. There are at most 3p+2 distinct marks. Between consecutive marks, every unmarked instruction is a square.

A marked nonsquare must immediately follow the preceding mark. Otherwise its predecessor would be an unmarked square m=b² with b≥2. If the nonsquare did not read m, its product would be at most b²=m and its sum at most 2b≤m, contradicting strict increase. Reading m would itself make that predecessor a mark.

Therefore each transition between marks is either a nonsquare with two references to earlier marks, or a positive-length run of squares starting at the preceding mark. For bounded p there are finitely many such controls. Only the square-run lengths vary. If a control has p nonsquares and square lengths g₁,…,g_d, its instruction count is

    r = p + Σgᵢ.

With p nonsquares there are at most 3p+1 block transitions and at most 2p+1 square-run parameters. There are finitely many operation labels and references to earlier marks at each of these boundedly many positions. This representation retains every nonsquare operand even when it lies inside a long run. The implemented encoder reconstructs the full numerical chain, with canonical normalization of 2→4. The Lean module ChainCoverage now proves that a nonsquare predecessor is marked, that a nonsquare boundary is adjacent to its preceding mark, and that a square boundary is exactly the iterated square of that mark. It formalizes these local coverage steps for every chain satisfying its explicit increasing-AM definition. [Encoder and decoder](../../solved/square_controls.py)

## 3. Domination when square parameters increase

Fix one control. Increase one run length by one while keeping every other parameter fixed. At the changed mark the new saved value is the square of its old value. Previously saved values remain unchanged and are bounded by their own squares. Thereafter multiplication preserves the coordinatewise squared bound. Addition preserves it because

    x²+y² ≤ (x+y)².

An unchanged square run preserves it too. Consequently the new endpoint is at most the old endpoint squared, while the written length increases by one. This is an algebraic assertion about positive expressions, valid even if an intermediate parameter choice loses the strictly increasing order required for a canonical chain.

Iterating the comparison gives the following. If g≤h coordinatewise and their length difference is q=Σ(hᵢ−gᵢ), then

    endpoint(h) ≤ endpoint(g)^(2^q).

The existing Lean lemma one_extra_square checks the single insertion comparison for arbitrary saved histories and fixed suffix instructions. The passage to repeated insertions is induction. [Kernel-checked comparison](../../lean/MarkedComparison.lean)

## 4. The contradiction

Fix an arbitrary integer C≥0. Suppose infinitely many n admit an AM chain for Nₙ of length r≤n+C. Since Nₙ exceeds the maximum attainable in n instructions, r≥n+1. Also λ(Nₙ)=n, so s≤C and p≤6C+2. Choose a witnessing chain for each n.

There are finitely many values of r−n and finitely many controls. On an infinite subsequence both the excess j=r−n and the control are fixed. Sort this subsequence by n. Dickson's lemma supplies two indices n<m whose square-run vectors are coordinatewise ordered. Their length difference is exactly m−n, so the domination inequality gives

    Nₘ ≤ Nₙ^(2^(m−n)).

But Aₘ=Aₙ^(2^(m−n)), and for any integer A≥2 and exponent q≥2,

    A^q−1 > (A−1)^q.

Hence Nₘ>Nₙ^(2^(m−n)), the contradiction. It follows that for every C only finitely many n have τ₊(Nₙ)≤n+C. This proves τ₊(Nₙ)−n→∞. The signed program writes 2, squares n times, and subtracts the saved 1, using n+2 instructions. The Lean theorem finite_descriptions_obstruction now checks the contradiction for any supplied finite family satisfying the coordinate-domination property. It encodes the finite control and excess as a bounded label together with its complement; coordinatewise comparison forces label equality. Padding the run vector with zeros allows a fixed dimension. Connecting every arithmetic chain to that finite-family hypothesis remains part of the written proof. The additive gap therefore tends to infinity. Dickson's lemma also underlies the independently stated [AM-defect well-ordering argument](../am-defect-order/PROOF.md); the direct argument here uses only integer endpoint comparisons after the coarse nonsquare bound.

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

## 7. What remains before an effective cutoff

Dickson's lemma proves the finiteness used in §4. Known quantitative bounds for bad sequences additionally require a control function restricting coordinate growth. The later theory of strongly monotone descending chains supplies sharper bounds under further hypotheses. Neither condition has been established for the witnesses here. In particular, the index of the next exceptional tower exponent could be very large compared with its position in a list of exceptions. We therefore do not claim an effective cutoff or a numerical rate for the additive gap. [Figueira et al., controlled Dickson bounds](https://arxiv.org/abs/1007.2989) · [Schmitz and Schütze, ICALP 2024](https://doi.org/10.4230/LIPIcs.ICALP.2024.153).

The exclusion certificate is useful even without such a cutoff: any verified base removes all its strict coordinate extensions at the same control and excess. A complete search must still account for every control and every remaining incomparable region. A new representation or arithmetic argument may be needed to make that coverage effective.

## Verification scope

The finite-control encoder, reconstruction and one-square inflation are tested on all at-most-two-small-step chains through 10^18 and further small cases. Additional tests compare exclusion certificates against exact small endpoints, preserve an exact base solution, reject incomparable parameters, and test membership with an exponent parameter of 10^100 without expanding that candidate.

Lean checks local chain coverage, the single-insertion comparison, finite-dimensional thinning, the strict tower-minus-one power gap, upward-region exclusion and the finite-family obstruction under its stated domination hypothesis. Chain normalization from general AM programs, the nonsquare count bound, finite-control packaging and the resulting end-to-end asymptotic conclusion remain written arguments. The Python encoder is tested, not formally verified. Independent review is pending. This is a proposed resolution of the additive-gap question; it establishes no polynomial separation and claims no publication priority.
