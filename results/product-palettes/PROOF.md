# Product constraints over finite palettes: feasibility and costs

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

Choose positive integer factors from explicit finite palettes, subject to product interval constraints. Feasibility and different cost objectives have distinct complexity.

**Feasibility theorem.** For each unknown xᵢ supply a finite nonempty set Dᵢ of positive integers. For every constrained pair impose Lᵢⱼ≤xᵢxⱼ≤Uᵢⱼ. Feasibility, including loops, parallel constraints, arbitrary graph structure and arbitrary error widths, reduces exactly to 2-SAT. Let D be the total palette size. The reduction uses at most D+1 Boolean variables and O(D+Σᵢⱼ min(|Dᵢ|,|Dⱼ|)) clauses, with binary-search overhead for locating bounds in the other palette. Once constructed, strongly connected components solve it in linear time.

**Construction.** Sort each palette as d₀<…<dₖ. Use the threshold literal Xᵢ,r for xᵢ≥dᵣ, treating the first threshold as true and the threshold past the last entry as false. Add implications from each higher threshold to the preceding one. Their truth assignments represent exactly one palette value.

For an edge, enumerate each a=dᵣ from the smaller palette. The upper product bound gives

    xᵢ≥a implies xⱼ≤floor(Uᵢⱼ/a).

Represent it as a binary clause forbidding both threshold events. The lower bound gives

    xᵢ≤a implies xⱼ≥ceil(Lᵢⱼ/a),

another binary clause, using the next threshold for the negation of xᵢ≤a. Bound searches skip gaps in a palette exactly. For an actual selected xᵢ=a, these two clauses force precisely the permitted interval for xⱼ. Every other clause is necessary for any feasible product. This proves equivalence. Loops simply use literals from the same threshold family. Exact integer division handles bounds of any bit length.

This is a specialization of established order encodings and tractable binary constraint languages. The product-specific construction supplies a compact implementation and permits arbitrary finite source palettes. Its polynomial bound is in the explicit palette size, which can itself be large. [Connected row-convex constraints and threshold clauses](https://ijcai.org/proceedings/2009/78) · [Related variable-elimination algorithm](https://ijcai.org/proceedings/2007/0029.pdf)

## What source-cost objective is tractable?

Give each palette occurrence a nonnegative construction-cost upper bound. The minimum possible **largest** individual source cost is polynomial-time computable. At a cost threshold retain only values with some source recipe at or below the threshold, then solve the 2-SAT instance. Feasibility is monotone in the threshold, so binary search over the distinct costs finds the exact bottleneck optimum.

The sum of unary costs is already NP-hard. Give every vertex of a graph the palette {1,2}, costing zero and one respectively. On each edge require 2≤xᵢxⱼ≤4. This forbids assigning 1 to both endpoints. Thus the vertices assigned 2 form a vertex cover and the total cost is its size. Construction sharing makes the actual instruction-cost problem different again. A bottleneck optimum therefore supplies a grounded candidate family when each palette entry has a valid source; it does not optimize a shared arithmetic circuit.

The implementation reuses SymPy's existing strongly connected component algorithm. Six hundred small random problems are compared with exhaustive assignments and bottleneck costs. Tests include empty and duplicate palettes, self-constraints, large integers, contradictory bounds and the vertex-cover construction. [Implementation](../../solved/product_palettes.py) · [Tests](../../tests/test_product_palettes.py)

## Relationship to narrow-error reconstruction

The [narrow-error theorem](../narrow-products/PROOF.md) works with implicitly represented integer intervals in polynomial bit complexity. This method works with arbitrary explicitly enumerated palettes, admits wide errors, and can filter by known source costs. Together they provide two complete numerical procedures for different input representations. Both procedures assume the observation graph is supplied. They solve numerical constraints in their stated representations.

## Sharp tractability of cost selection under narrow errors

In a connected component satisfying the narrow-width condition, each fixed factor value admits at most one value at every neighbor. Therefore a root factor determines the entire tuple. With explicit palettes, enumerate the smallest palette and propagate each root through a spanning tree, rejecting missing neighbors and failed non-tree observations. There are at most minᵢ|Dᵢ| feasible tuples. After sorting the palettes, membership hash sets give O(minᵢ|Dᵢ|·(|V|+|E|)+Σ|Dᵢ|) arithmetic operations. This works for bipartite components as well as odd cycles.

Consequently any explicitly evaluable objective can be minimized over this tuple list. In particular, summing the supplied source costs is polynomial in the narrow regime. An objective may also count the union of fixed, already-supplied source recipes, provided evaluation includes their dependencies. Choosing among arbitrarily many alternative source recipes or proving a bounded-register optimum is an additional problem.

The width boundary is sharp for polynomial sum-cost selection unless P=NP. For any fixed positive m, give each graph vertex the palette {m,m+1}, with costs one and zero respectively. On each edge require m²≤xᵢxⱼ≤m(m+1). Its width is exactly m. The constraint forbids assigning m+1 to both endpoints, so the m-valued vertices form a vertex cover and the summed cost is its size. This gives hardness at equality with the factor lower bound. Below that boundary, every connected component has the polynomial enumeration above. [Exact enumeration and cost tests](../../tests/test_product_palettes.py)
