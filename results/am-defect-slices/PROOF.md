# The proposed sharp type of each bounded AM-defect slice

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

**Claim.** With the definitions in C13, for every integer k≥1 the usual order on D_AM∩[0,k) has ordinal type **ω^k**. Together with well-ordering and the global type ω^ω, this addresses all three clauses of Altman's AM-chain Question 6.2.1 in this model. This is a research proof; the ordinal conclusion has not received independent peer review or a full proof-assistant verification. [Original question, §6.2](https://hjaltman.github.io/thesis-FIXED.pdf) · [Lower bound and ordinal lemmas](../am-defect-order/PROOF.md)

C13 proved the lower bound. The missing upper bound needs a finer parametrization: square-run lengths in an endpoint description are more numerous than the real-error terms in its normalized logarithm.

## 1. One scalar of a discrete type per reset

Fix k and use q=k+ceil(log₂(6(k+1))) as in C12. Take any shortest chain contributing to this slice. Its integer defect is at most k. There are at most k post-prefix resets (late additions or multiplications with a far operand), uniformly finitely many nonsquares, and at least one operand of every late step lies within the recent window. Write t=i+1 for the new position, j for the *later* operand index, l for the earlier one, and put U_j=log₂(a_j)/2^(j−1) at j≥1. Set U₀=0 to handle the initial 1. The witness defect is −log₂ Uᵣ.

For a far multiplication the exact update is

    U_t = 2^(j−t) U_j + z U_l,      z = 2^(l−t).

For an addition it is

    U_t = 2^(j−t) U_j + z,          z = log₂(1 + a_l/a_j) / 2^(t−1).

The recent coefficient is fixed by a bounded operand lag. A far multiplication's z belongs to the positive dyadic reciprocals. For addition, 0<z≤2^(1−t) by chronological monotonicity. At fixed t the finite collection of legal arithmetic prefixes gives only finitely many possible z. Consequently each kind of z has finitely many distinct values ≥ε for every ε>0. In decreasing order the attainable values can be indexed by a subset of ℕ (a finite set or a sequence tending to zero). This treats the entire addition correction as *one* scalar, regardless of how many old operands were needed to compute it.

## 2. Finite controls give monotone functions of at most k scalars

Use the bounded prefix and the marked far reads as in C12. Track normalized logs throughout. A square copies the preceding U exactly. An ordinary nonsquare multiplication gives a linear combination of two recent normalized logs with positive dyadic coefficients from a fixed finite set of lags. A run of q squares makes the last q normalized logs identical. All extra copies in a longer run can therefore be erased in this calculation. If a future far multiplication reads from inside a long run, first split at that operand mark and retain its normalized value. Finite control consists of prefix choices, ordinary multiplications with their bounded offsets, bounded clipped runs, reset types, recent offsets and references to saved positions. The number of all such controls depends only on k by the nonsquare and reset bounds. Absolute time indices needed by a reset are absorbed into its z; they are not additional parameters of the function.

Induction on the clipped control gives Uᵣ=P(z₁,…,zₑ), e≤k, with nonnegative coefficients. Bounded prefix logs are nonnegative constants. Each ordinary update adds or multiplies by a nonnegative constant. Each far reset additionally multiplies a saved normalized log by its new z; an addition adds its new z. Increasing a parameter can never decrease P. Since −log₂ is decreasing on the positive range and each coordinate is indexed in *decreasing* order of z, the actual defects for this control are a coordinatewise nondecreasing image of a subset of ℕᵉ. Correlations between the z values can restrict that subset and do not invalidate monotonicity. The polynomial may use real constants. No approximation or numerical ordering test is used in this argument.

## 3. A parameter must be bounded on every proper initial segment

For an actual reset the recent-operand contribution is at most half the head just before the step, even when that operand is not the previous term: a_j≤aᵢ. The remaining contribution is at most z since any saved U_l≤1. Between resets U cannot increase. Starting with prefix head at most 1 and iterating gives Uᵣ≤2^(−e)+Σ zᵢ.

Fix any c<k and consider d≤c. When e=k, Uᵣ≥2^(−c) forces some zᵢ≥(2^(−c)−2^(−k))/k>0. There are only finitely many possibilities for that coordinate and its position. The remaining domains now have dimension at most k−1. When e<k they had this dimension bound already. The finite-image lemma of C13 bounds each monotone control range by ω^(k−1). The finite-color lemma then bounds their finite union *strictly below* ω^k. The same reasoning includes the finite prefix-only cases and k=1 (only finitely many values below any c<1).

If the slice's type exceeded ω^k, some element of the slice would have an initial segment of type ω^k. Taking that element as c gives a contradiction. Thus the slice has type at most ω^k. The nested square-plus-one witnesses and their finite coloring by actual shortening in C13 give the matching lower bound. This argument uses positive monotone AM chains from 1; negative intermediates, subtraction and division do not obey the required bounds.

**Verification scope.** The executable checker constructs the normalized polynomial of concrete witnesses, records the reset atoms, checks nonnegative coefficients and reconstructs the final integer via exact rational products. The generic monotonicity of positive expressions is also checked by the Lean kernel. Neither finite samples nor that monotonicity lemma alone establishes the ordinal theorem. [Exact normalized-mass checker](../../solved/normalized_mass.py) · [Formal monotonicity lemma](../../lean/PositiveExpressions.lean) · [Lean finite-dimensional no-descending-sequence lemma](../../lean/FiniteControls.lean).
