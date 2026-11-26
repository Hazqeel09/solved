# Factor recovery through guarded arithmetic paths

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

Consider a bounded positive-integer arithmetic path applied to an unknown factor product, with its output constrained to an integer interval. Side operands are fixed; a repeated-operand step uses the current value twice.

Backward analysis of program structure is an established synthesis technique. The 2026 work by Lee, Lee and Yi demonstrates why choosing holes that permit useful backward propagation affects search. Here we derive the transfer rules and the reconstruction theorem for positive exact arithmetic. [POPL 2026](https://doi.org/10.1145/3776694)

## Exact path guards and sound inverse intervals

Start with the terminal interval clipped to [1,C]. For each reversed path instruction, intersect its following inverse interval with [1,C]. The bounds are inclusive and all rounding is exact.

| Forward operation | Inverse interval for output in [L,U] |
|---|---|
| x+k | [L−k,U−k] |
| x−k | [L+k,U+k] |
| k−x | [k−U,k−L] |
| kx | [ceil(L/k),floor(U/k)] |
| x/k, exact | [kL,kU], with divisibility checked during replay |
| k/x, exact | [ceil(k/U),floor(k/L)], with divisibility checked during replay |
| x+x | [ceil(L/2),floor(U/2)] |
| x×x | [ceil(√L),floor(√U)] |
| x/x | [1,C] if the output interval contains 1, otherwise empty |
| x−x | Empty under the positive-value rule |

Each rule follows by solving the corresponding inequality over positive integers. An empty interval proves that the path has no legal input. Induction over reversed instructions proves that every legal input survives the complete backward pass. For division-free paths the resulting interval is exact. With division, intermediate integrality conditions can leave holes, so the path is retained and replayed at any inferred factor assignment. Intersecting with the cap at every step prevents an overflowing operation from being legitimized by a later cancellation.

For example, dividing by 2 and then multiplying by 2 can leave the integer interval [2,4] from an output interval [2,4]. Input 3 remains in the interval but fails exact replay. Multiplying by 2 before dividing by 2 cannot take input 9 through a cap of 10, even though its simplified rational expression equals 9.

## Complete reconstruction theorem for the extended model

Let the backward product intervals be Iₑ=[Lₑ,Uₑ]. Suppose their graph is connected, every width is below both endpoint factor lower bounds, and the graph has an odd cycle or an exact anchor. Then the following procedure is complete.

1. Recover the unique possible factor tuple from Iₑ using the integer product algorithm.
2. Execute every original path on its factor product, checking positivity, cap and exact division at every instruction.
3. Verify each observed output interval.

Every legal assignment satisfies the relaxed product system. That system has at most one assignment under the [narrow-error theorem](../narrow-products/PROOF.md). Therefore a failed replay of its unique candidate proves infeasibility for the original guarded system. A successful replay supplies the unique legal assignment. If the product system is unanchored and bipartite, its explicit-palette enumeration can instead enumerate all candidates and apply the same guards to each.

The algorithm has polynomial bit complexity in the encoded paths, graph and bounds. Repeated squaring may give an expanded polynomial exponential degree in path length; the backward algorithm keeps the program representation and uses integer square roots. This result concerns the stated path structure and uniqueness condition.

## Verification

Tests compare backward intervals against every input in 1,600 small random path problems. Division-free preimages agree exactly; all legal inputs survive the division relaxations. Another 180 complete factor-assignment checks cover scaled and shifted triangles. Repeated squaring, large magnitude limits, empty preimages, intermediate overflow and one-shot path iterators are tested explicitly. [Implementation](../../solved/path_intervals.py) · [Tests](../../tests/test_path_intervals.py)
