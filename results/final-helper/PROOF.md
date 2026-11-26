# A complete finite menu for the final helper

**Status: research proof draft; independent mathematical review pending.** Automated evidence is scoped below and does not certify the complete argument.

With unrestricted retention, target saturation restricts the final helper to an exact finite backward menu. Earlier helper choices may be arbitrary.

Let K be a nonempty available bank closed under producing the required targets T. Suppose some targets remain missing and exactly one helper h remains to be written. Then every successful continuation has an equally short continuation with h in the following menu.

- For each missing target t and k∈K, invert each legal ordered arithmetic equation t=op(h,k) or t=op(k,h).
- Include t/2 when t is even and √t when t is a perfect square.
- Keep only positive, cap-respecting values obtainable in one operation from K, excluding already-available values.

There are at most (6|K|+2)|T∖K| candidates before deduplication. The menu gives a necessary condition. Each candidate still has to pass target saturation; a fixed storage bound requires separate scheduling.

**Proof.** Saturation ensures no missing target can be written using K alone. With h as the last helper, the first new write after h must be a target t. If it uses h and a member k of K, one of the inverses enumerates h. If it uses h twice, positive addition gives h=t/2 and multiplication gives h=√t. Subtraction gives zero and is illegal. Self-division gives t=1, but 1 would already be reachable by dividing any k∈K by itself and would have entered the target closure. Thus the list is exhaustive. Conversely every candidate has a grounded helper recipe, and subsequent saturation explicitly checks whether it reaches all targets. Combining this lemma with arbitrary earlier helper branching preserves the completeness theorem. [Underlying target-saturation proof](../target-saturation/PROOF.md) · [Published generalized-SLP direction](https://doi.org/10.4230/LIPIcs.CP.2026.11)
