# Sharp counting order for shortest defect-two endpoints

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

**Claim.** In monotone addition–multiplication chains from 1, let δ(n) be minimum length minus the integer level λ(n). Let H₂(N) count distinct n≤N with δ(n)=2. Then H₂(N)=Θ((log log N)⁵). More precisely, at every sufficiently large complete level L, the number of distinct shortest-defect-two endpoints is Θ(L⁴). This is a counting theorem for the full class. It does not list all shortest chains or establish priority over the literature. The five-parameter construction and decoder are executable. [Construction](../../solved/counting.py) · [One-defect precedent](https://doi.org/10.3934/Math.2026667) · [Canonical nonsquare bound and square stability](../seven-nonsquares/PROOF.md).

## Lower bound and explicit inverse

Write Tₖ=2^(2ᵏ). Choose integers 0≤j<i<k, h≥1 and d≥0. Set A=Tₖ, B=Tᵢ, C=Tⱼ and form

    u = A+B,   X = u^(2^(h−1)),   y = X²+C,   n = y^(2^d).

Start with the whole tower prefix through A. Add B, square h times, add C, then square d times. Both additions preserve the level. For the first addition A<u<A². For the second, A^(2^h)≤X²< X²+C <(A²)^(2^h): already A²−u>C and powering gives at least as large a gap. All other writes starting from A are level-increasing squares. The final level is L=k+1+h+d and the witness uses L+2 writes.

To prove shortestness, first observe y is even and strictly between X² and (X+1)² since 0<C<2X+1. In X² the lowest set-bit position is 2^(i+h), while C has its only set bit at position 2^j. X² is not a power of two, so y has at least three bits set. By the published one-defect families, an even nonsquare of defect at most one has at most two set bits. Therefore δ(y)=2, and C8's square stability gives δ(n)=2.

These parameter tuples never collide. Extract integer square roots from n while exact to obtain y and d. Now floor(sqrt(y))=X, so subtraction recovers C and its tower index j. The integer u=A+B is nonsquare: its odd part is 1+2^(2^k−2^i) with a positive even exponent since i≥1. This odd part lies strictly between consecutive squares. Thus repeated exact square rooting of X recovers u and h. Its two bit positions uniquely recover k and i. This gives a bijection onto the constructed subfamily.

At fixed L there are Σ from k=2 to L−2 of binom(k,2)(L−k−1) such tuples. Choose i and j among k lower tower indices, then distribute L−k−1 between h≥1 and d≥0. Two applications of the hockey-stick identity give **binom(L,4)**. The constructed count through complete level K is binom(K+1,5).

## Upper bound by charging operand and gap choices

Take any witnessing chain with at most two small steps. After the prefix 1,2,3 or 1,2,4, record each canonical nonsquare together with its preceding gap of successive squares. There are at most seven canonical nonsquares in the whole chain by C8. For a nonsquare from the current greatest term aᵢ, mark G if the preceding recorded square gap is positive and F if the smaller operand index is at most i−6. The final trailing square gap is handled separately.

For every i≥1 let uᵢ=log₂(aᵢ)/2^(i−1). One has 1/4≤uᵢ≤1 along a chain of defect at most two. Maximum growth by squaring makes u nonincreasing; squares preserve it. If G occurs, the penultimate term is the square root of aᵢ. Even the maximal nonsquare aᵢaᵢ₋₁ gives uᵢ₊₁≤(3/4)uᵢ. This uses aᵢ₋₁≥2 after the specified prefix. If F occurs, i≥6. For multiplication the older operand's log divided by 2^i is at most 2⁻⁷, since aⱼ≤2^(2^(j−1)) for j≥1 and log(1)=0. For addition use aᵢ₊₁≤2aᵢ, contributing at most 2⁻⁶ past uᵢ/2. In either case uᵢ₊₁≤uᵢ/2+1/64≤(9/16)uᵢ. Thus an event with both marks pays two factors of 3/4; either single mark pays at least one such factor. Since (3/4)⁵=243/1024<1/4, **the entire chain has at most four marks**, counting coincident marks twice.

At least one operand of every step must be among the three most recent terms. Otherwise, for i≥4 both operands are at most aᵢ₋₃≤2^(2^(i−4)). Their sum and product are no greater than 2^(2^(i−3))≤aᵢ; the tiny initial cases follow directly. At an unmarked near-operand step both indices therefore have only a constant number of choices; a far step has at most O(L) choices since the other index is one of the last three. Each positive square gap has O(L) possible lengths. There are only constantly many choices of nonsquare count, mark positions, binary operation labels, and initial prefix. For a shortest defect-two endpoint on level L the length is fixed at L+2. Once the nonsquares and their gaps have been described, the trailing square count is forced. Thus O(L⁴) descriptions suffice; distinct descriptions can give the same endpoint, which preserves the upper bound.

For arbitrary cutoff N let K=λ(N). Every level below K is complete, yielding at least binom(K,5) constructed endpoints for large K. Summing the per-level upper bound through K gives O(K⁵). Since K differs from log₂ log₂ N by a bounded amount, the claimed asymptotic order follows.

This counts distinct integers in the specified monotone model; it is not a bound on arbitrary arithmetic circuits.
