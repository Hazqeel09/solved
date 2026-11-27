# Formal statement correspondence

The complete formalization covers the three exact increasing-AM costs and
the failure of uniform marked square-root reconstruction at defect at most
two. It is implemented in [RootRetention.lean](../../lean/RootRetention.lean),
reusing [SquareInstability.lean](../../lean/SquareInstability.lean).

| Mathematical claim or object | Lean statement or definition |
|---|---|
| Natural-number +/× writes with unrestricted reuse | Existing `Recipe` and `Reach` |
| End at a target while retaining a designated value | `MarkedReach target mark cost history` |
| A marked computation is an ordinary AM computation | `forget` |
| A missing marked value must exceed the current head | `future_mark` |
| Complete marked search, with existing endpoint-search delegation | `markedSearch`, `marked_search_complete` |
| No five-write program for 2000 | `no_five_for_root`, `root_lower` |
| No six-write program for 4,000,000 | `no_six_for_source`, `source_lower` |
| No six-write joint program for 2000 and 10 | `no_six_with_mark`, `marked_lower` |
| Explicit six-/seven-write upper bounds | `root_upper`, `source_upper`, `marked_upper` |
| The exact costs 6,7,7 | `exact_costs` |
| Level five and cost seven for the source | `InLevel`, `source_level` |
| A shortest source of defect ≤2 need not have a shorter marked-root program | `no_uniform_root_retention` |

The universal assertion negated by `no_uniform_root_retention` quantifies
over source endpoint N, a retained value m, their roots R,M, the minimum
source cost r and a positive level L. It requires a shortest source of cost
r≤L+2, and demands a marked root program of cost strictly below r. The
formal counterexample instantiates these parameters with
N=4,000,000, m=100, R=2000, M=10, r=7, L=5.

`InLevel n L` means 2^(2^(L−1))≤n<2^(2^L), with L>0 in the quantified
claim. This is the integer form of the AM level. Thus the counterexample
has minimum defect exactly two. The source proof explicitly visits 100;
the root and joint upper proofs explicitly charge every instruction from 1.

The marked search uses the same complete all-pairs `options` and safe
maximum-growth test as the existing endpoint search. Its additional
missing-mark pruning is justified by `future_mark`. Lower bounds depend
on completeness; upper bounds are explicit relation proofs, so no
unproved search-soundness assertion is needed. The closed exclusions use
ordinary kernel `decide`, not native execution certificates.

This complete-formalization label does not include the generic Python menu
solver, its generic multi-output optimality argument, the separate 640
menu-gap control, or a model with subtraction, division, arbitrary seeds or
nonincreasing writes. It does not assert that the example was previously
unknown, establish independent review, or resolve unmarked root closure.
