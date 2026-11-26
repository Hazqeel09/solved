# Unique integer recovery from narrow product intervals

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

Recover hidden positive integer factors from a graph of bounded-error product observations.

Graph-based identifiability for symmetric rank-one matrix completion is established in the literature. Ma et al. identify the role of non-bipartite connected components for real factors. We derive the following sharp integer specialization with an exact reconstruction algorithm. It uses discrete spacing and explicit error intervals. No priority claim is made for the underlying graph criterion. [Ma et al., JMLR 2020](https://jmlr.org/papers/volume21/19-359/19-359.pdf)

## Theorem and sharp threshold

Let G be a connected graph, allowing loops and parallel edges. Unknowns xᵢ are positive integers in stated finite domains [mᵢ,Mᵢ]. Each edge ij constrains its product to a known integer interval [Lᵢⱼ,Uᵢⱼ]. Suppose every interval has width

    Uᵢⱼ − Lᵢⱼ < min(mᵢ,mⱼ).

If G has an odd cycle, there is at most one feasible tuple. The same conclusion holds for any connected G when one coordinate is anchored exactly. A complete algorithm finds that tuple or proves infeasibility using O(|V| log M + |E|) arithmetic operations, where M is the largest domain upper bound. Its integer bit complexity is polynomial in the input length.

For a uniform factor lower bound m and observations |xᵢxⱼ−tᵢⱼ|≤E, the condition becomes **2E<m**. This uniform threshold is sharp. With m=10, domains [10,11], and observations 105,105,100 on a triangle with E=5, both (10,10,10) and (11,10,10) fit. In general, let the first two observation intervals be [m²,m²+m] and the third [m²,m²]. Both (m,m,m) and (m+1,m,m) fit. For even m these are symmetric noise intervals with E=m/2. Thus a uniform guarantee cannot include equality at 2E=m.

**Uniqueness proof.** Compare two feasible assignments x and y. If some coordinates agree and some differ, connectedness supplies an edge between these groups. Its product changes by at least the unchanged endpoint's value, hence at least its domain lower bound, exceeding the observation width. If every coordinate changes, classify vertices by the sign of xᵢ−yᵢ. A non-bipartite graph has an edge whose endpoints have the same sign, including a loop. Along that edge the product changes by at least the smaller endpoint lower bound, again exceeding its allowed width. An exact anchor ensures the first case whenever two distinct assignments are compared. Both cases contradict feasibility.

An unanchored bipartite component has no such uniform guarantee, even with exact products. Assign all vertices on one side 2m and the other side 3m. Swapping these values preserves every product. Particular domain restrictions can still make a bipartite instance unique; the algorithm below returns undetermined for this unsupported case.

## A complete reconstruction algorithm

For an edge ij define a total map on the domain of xᵢ by

    Fᵢⱼ(a) = clamp(floor(Uᵢⱼ/a), mⱼ, Mⱼ).

It is non-increasing. Any feasible neighbor b must equal Fᵢⱼ(a). Indeed L≤ab≤U and U−L<a imply U<ab+a, so floor(U/a)=b. The clamp makes the map total while leaving every feasible pair intact. These maps are candidate transports; all original interval inequalities are verified at the end.

If a coordinate is anchored, propagate its value through a spanning tree and verify every edge. Otherwise choose an odd closed walk. A spanning tree and an edge joining equal depth parities supply one of length at most 2|V|−1. Composing its maps gives a non-increasing self-map F of the root's domain. Any feasible root satisfies F(a)=a. Such a map has at most one integer fixed point. Find the largest a with F(a)≥a by binary search. If equality fails there, no feasible root exists. Otherwise propagate this root through the tree and check every product interval. A failed check proves infeasibility because every feasible assignment would have followed the same transports and fixed point. A passed check gives the unique tuple.

This algorithm avoids enumerating the root domain or factoring the observations. The strict-width condition is essential for the transport equality. Beyond it, choosing the uppermost permitted neighbor can discard other feasible solutions.

## Worked example

Suppose three product observations are 10,809, 11,661 and 11,010, each with error at most 3, and the factors lie between 7 and 20,000. The algorithm recovers (101,107,109). Their products are 10,807, 11,663 and 11,009, so the signed residuals are 2, −2 and 1. The factor values and residuals are inferred from the observations. The theorem concerns numerical recovery from the observations.

## Verification and application contract

Independent exhaustive assignment enumeration checks 750 small connected instances, with varying domains, inconsistent observations, self-loops, parallel edges, anchors and sharp-boundary counterexamples. Additional tests recover large factors on a five-cycle and an anchored tree using at most 62 root-map evaluations. The implementation uses exact integer division throughout. [Implementation](../../solved/product_intervals.py) · [Tests](../../tests/test_product_intervals.py)

Lean checks integer transport, unique neighbors and fixed-point uniqueness. The global graph argument and complexity bound remain written. [Formal lemmas](../../lean/ProductIntervals.lean).
