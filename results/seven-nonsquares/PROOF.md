# Twelve squaring rays with seven canonical nonsquares

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

**Theorem (unbounded, value sequences).** Start at 1 and increase strictly, using additions and products of any two earlier terms. Call a write a canonical square when the new number equals the preceding number squared. Exactly seven canonical nonsquares and exactly two small steps are possible. Eight canonical nonsquares are impossible with at most two small steps. The endpoints in the seven case are precisely the twelve squaring rays below. A ray with base b consists of b, b², b⁴, … . The eight rows marked 2 are exactly the rays admitting a *shortest defect-two chain* with seven canonical nonsquares.

| Base | Minimum defect everywhere on its ray |
|---:|---:|
| 69,984 | 2 |
| 84,375 | 2 |
| 209,952 | 2 |
| 7,346,640,384 | 2 |
| 10,460,353,203 | 2 |
| 11,019,960,576 | 1 |
| 13,060,694,016 | 2 |
| 14,693,280,768 | 2 |
| 17,179,869,184 | 1 |
| 18,446,744,073,709,551,616 | 0 |
| 28,430,288,029,929,701,376 | 2 |
| 36,893,488,147,419,103,232 | 1 |

The convention at 2→4 matters. The labelled instruction 2+2 produces the same value as a square. It contributes one additional nonsquare under an operation-labelled convention; this is the only such ambiguity because m²>2m for m>2 and no other pair of previous values has product m². The table classifies the normalized value sequences. It is a subcase of the general classification problem in §7 of Tarek, Bahig and Anwar. We use their maximal nonsquare idea and Theorem 1.2. The all-length gap and deviation certificate below specializes and sharpens the count bound in their Corollary 3.1. No precedence claim or full proof-assistant formalization is made. [Published paper, pp. 16239 and 16242](https://doi.org/10.3934/Math.2026667)

## 1. A finite signature for arbitrarily long chains

The first three terms are 1,2,3 or 1,2,4. For subsequent nonsquares write M for attaining the largest permitted nonsquare value and D for an actual smaller value. Record also the number of intervening squares before each nonsquare; trailing squares do not affect defect. With current three largest terms m>k>z, the M envelope is mk. At the exceptional first transition with k=2, the next distinct value below that envelope is m+k. At all other transitions z≥2, and the largest value below mk allowed by a nonsquare is max(mz,k²). Indeed every other product is bounded by one of these two and every sum is at most 2m≤mz. Both upper bounds are attained by legal writes. The first exceptional transition can be checked from the three available terms.

For a fixed M/D signature, using these respective envelopes at every step maximizes the final endpoint. Induct on the prefix: a square and both envelope formulas are componentwise monotone in the largest three terms. The initial exceptional case is common to every chain of that signature. Thus a smaller D choice cannot make an otherwise infeasible signature feasible.

Let uᵢ=log₂(aᵢ)/2^(i−1) for i≥1. At positive length i, defect at most two is equivalent to uᵢ≥1/4. A square leaves u unchanged. For M, the next normalized value is uᵢ/2+uᵢ₋₁/4. For the nonexceptional D envelope it is max(uᵢ/2+uᵢ₋₂/8, uᵢ₋₁/2). Two or more consecutive squares leave the three most recent normalized values equal. Hence each gap needs only the symbols 0, 1 or 2 (the last means at least two). For M alone, one square suffices to reset the last two, so its gap symbols are just absent/present. This reduction in the number of signatures is exact for arbitrary lengths. A prefix already past defect two can be discarded because a level can increase by at most one per write.

## 2. Exact finite exhaustion and reconstruction

Use five remaining nonsquares after 1,2,3 and six after 1,2,4. For each compressed gap word and D subset evaluate its envelope, comparing integer bit lengths at each step. This requires at most 6⁶ signatures per initial case. The complete enumeration, with surviving signatures and one recipe-independent value witness per base, is recorded in [the certificate](../../checks/expected/seven-steps.json) and [the verifier](../../solved/seven_steps.py). A second verifier performs the normalized recurrences on rational coefficient vectors for log₂ 2, log₂ 3 and log₂ 5. It compares linear forms by integer prime products. Both methods give 17 admissible compressed signatures from 1,2,3 and 21 from 1,2,4. [Independent calculation](../../checks/verify_seven.py).

- After 1,2,3 with M steps only, the positive gaps can occupy no position, any single position among 1–5, or precisely positions 2 and 4.
- After 1,2,4 with M steps only, gap 1 is free. Among the remaining gaps, either all are zero or exactly one of positions 3, 4 or 5 is positive.
- There are precisely two admissible signatures containing D. Both start 1,2,3 and have no intervening squares. D is at position 1 or 4 among the five remaining nonsquares. Enumerating every value below the M envelope at that single step gives exactly the chains (1,2,3,5,15,75,1125,84375) and (1,2,3,6,18,108,648,69984). Every other post-prefix step in these chains is M.
- For an eighth nonsquare, even M at every position fails the threshold for every absent/present gap word. The same upper bound excludes every smaller nonsquare choice. Longer prefixes cannot repair the defect.

For each admissible all-M pattern, set its positive gaps to one to obtain its representative. At such a gap the two latest terms after squaring are powers of a single preceding term. Increasing the gap by one squares both of those values. All subsequent M operations multiply the two most recent terms, and subsequent squares square the head. Thus extending an already positive gap squares the old endpoint. Trailing squares realize every member of a ray. Deduplication by integer square roots gives precisely the twelve bases above. Every admissible envelope has defect exactly two. The representatives are constructive, with no limit on the number of appended squares.

## 3. A stability corollary for every shortest chain of defect two

Let δ(n)=ℓ_AM(n)−λ(n), for n≥2. **If δ(n)≤2, then δ(n²)=δ(n), and ℓ_AM(n²)=ℓ_AM(n)+1.** Induction gives the same conclusion along every squaring ray. This claim uses the published one-defect classification; it does not depend on belonging to the seven-nonsquare sector.

Appending a square shows δ(n²)≤δ(n). The zero-defect tower is closed under taking an integral square root. We show the union of the zero- and one-defect families in Theorem 1.2 is also closed under taking an integral square root. A positive outer squaring exponent can simply be reduced by one level. The odd bases 3 and 27 are nonsquares. The odd base 2^(2^α)+1 for α≥1 lies strictly between consecutive squares. The pure power with exponent 2^α+2^β has an integral square root only when β≥1, in which case halving the exponent keeps the same form.

The two remaining bases can be written 2^V(1+2^k). For an integer square, V must be even and the odd part must be square. The equation u²−1=2^k for odd u>1 gives u=3 and k=3, since u−1 and u+1 must be two powers of two differing by two. In both families k=2^α−2^β. To get 3 forces (α,β)=(2,0). The corresponding V is 1 or 5, both odd. This excludes an additional square at the base. It follows that δ(n²)≤1 implies δ(n)≤1. Combining the two root-closure statements with the appending bound proves stability up to defect two.

For each tabulated representative, test membership in the published zero/one families. Nonmembership proves minimum defect two because a two-step witness is supplied. Stability then propagates the result across its entire ray. The executable checker uses just exact integer square roots, bit counts, and the binary exponents of a two-term sum. The bounded exhaustive chain enumerator provides an independent test of all twelve base labels. This argument determines neither all two-small-step endpoints nor what happens when a higher-defect integer is squared.
