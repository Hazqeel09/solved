# A defect-two obstruction to retaining an earlier square root

**Status: proof draft; independent presentation and priority review pending.**
The exact minima and the counterexample to uniform marked-root reconstruction
are completely formalized in Lean. This is a locally posed strengthening of
root closure, not a conjecture attributed to the cited literature. The
unmarked defect-two root-closure question remains open.

## 1. Exact statement

An increasing addition–multiplication chain starts with 1. Every instruction
adds or multiplies two retained earlier values, including repeated operands,
and costs one write. Storage is unrestricted. There are no additional seeds,
subtraction, division or free square-root operations.

Let ℓ(n) be the minimum cost to end at n. Let ℓ(n; m) be the minimum cost
to end at n while also producing and retaining m. Then

    ℓ(2000)=6,      ℓ(4,000,000)=7,      ℓ(2000;10)=7.

The shortest seven-write source

    1,2,4,5,20,100,2000,4,000,000                         (P)

visits the square 100. Its endpoint is 2000² and has level
λ(4,000,000)=5, so its minimum defect is 7−5=2. A root program that
also retains √100=10 cannot save even one write. Thus the assertion

> Every shortest square-ended AM chain of defect at most two has a shorter
> root program that also produces the square root of any designated earlier
> square value.

is false. Requiring roots of *all* earlier square values is consequently
false as well. For P those roots are exactly {1,2,10,2000}.

This does not refute ordinary root closure: 2000 has level 4 and minimum
cost 6, hence still has defect two. It refutes a stronger property that
would have made composition of root constructions easier. In the event
notation of the root-sector manuscripts, P has word GSG followed by a
canonical square. The [GSG theorem](../root-closure-sectors/ONE-BIG.md)
requires only its endpoint root, which P obtains by deleting its last write.

## 2. Upper and lower certificates

The first six writes of P produce 2000. All seven writes produce its square.
A seven-write joint program is

    1,2,3,5,10,20,100,2000.                              (J)

In J, 10=2·5, 20=2·10, 100=10² and 2000=20·100. Thus the joint cost
is at most seven; the claim is not based on failing to find a convenient
formula.

The matching lower bounds use complete exact searches. The existing Lean
AM-chain search proves that no five-write chain reaches 2000 and no
six-write chain reaches 4,000,000. A marked extension proves that no
six-write chain ends at 2000 and contains 10.

The marked search reuses the existing all-pairs operation generator,
duplicate-removal proof, target cap and maximum-growth pruning. Once 10 is
present, it delegates to the existing endpoint search. Before 10 has appeared,
it discards a state whose head is at least 10: strict increase makes a later
visit to 10 impossible. The `future_mark` lemma proves this pruning rule;
`marked_search_complete` proves that every valid marked chain survives the
search. The three closed false search results are kernel reductions using
`decide`, with no external search assertion or additional trusted axiom.
The upper bounds are explicit legal-chain proofs.

An independent Python enumerator agrees. Its complete defect-at-most-two
census through 2000 visits 1,548 value sequences and finds exactly two
six-write endpoint histories:

    1,2,4,5,20,100,2000
    1,2,4,5,20,400,2000.

Neither contains 10. Since 2000 has level four, a chain ending there in at
most six writes has defect at most two and is included. The defect budget
cannot decrease along an increasing AM chain. The Lean marked search does
not rely on this defect-based pruning, providing a separate verification.

[Lean proof](../../lean/RootRetention.lean) ·
[Statement correspondence](FORMALIZATION.md) ·
[Independent checker](../../checks/verify_root_retention.py) ·
[Stored certificate](../../checks/expected/root-retention.json).

The exact lower bounds and the formal claim concern increasing AM chains.
No lower bound for a model permitting subtraction, division or external
constants is asserted.

## 3. Equal cost does not make histories interchangeable

Replacing the intermediate 100 in P by 400 gives another optimal source:

    1,2,4,5,20,400,2000,4,000,000.                        (Q)

Its earlier square roots are 1,2,20,2000. Deleting the last write produces
all of them in six writes. The two source histories have the same endpoint
and optimal cost, yet differ in whether all their square roots can be
preserved while shortening the final root computation.

This is why an endpoint theorem cannot be used as an automatic interface
for a shared computation. A replacement needs an explicit list of values
that the remaining program will read. Constructing every possible root can
itself consume the entire available saving.

The statement follows from the explicit programs and the exact costs above.
The companion Python check verifies Q and its retained roots; the separate
Lean universal counterexample needs only P and J.

## 4. A candidate-menu failure is a different kind of evidence

A useful positive control is the four-event exchange source

    1,2,4,16,64,80,6400,409600.

Its endpoint root is 640, and the earlier square roots include 8 and 80.
The previously proved *endpoint* menu contains a six-write program for 640,
but contains no six-write program satisfying the additional requirements
8 and 80. This alone is not an unrestricted obstruction. Adding the missing
helper 10 gives

    1,2,4,8,10,80,640,

where 10=8+2, 80=8·10 and 640=8·80. The independent witness proves that
six writes do suffice for these joint requirements. The earlier menu theorem
never claimed completeness for arbitrary marked outputs.

By contrast, the 2000 counterexample has a complete lower bound over all
legal increasing AM histories, independently of a candidate menu. These two
cases are regression tests for that distinction.

## 5. Exact finite-menu synthesis with required outputs

The existing [menu solver](../../solved/menu_programs.py) now accepts a
`required` collection of values that must appear before or at the final
target. Its arithmetic and retention model are unchanged. Only 1 is free;
all required values must be constructed from the menu by real writes.

For every value, retain inclusion-minimal ancestor-support sets as in
[the original support proof](../root-closure-sectors/FOUR-EVENTS.md).
At the end, combine a target support with a support for each required value
by set union, retaining the inclusion-minimal unions. This adds no fictitious
arithmetic gate. Each support union is executable in increasing numerical
order, and its cardinality is the actual number of noninitial writes.

For completeness, let P be any valid menu program satisfying the target
and every requirement. For each required output, including the target, an
inductively retained support is contained in P. Their union is also contained
in P and is executable. Subset dominance remains safe at each join because
all supports being compared already satisfy the same outputs, and union
with future supports preserves inclusion. A minimum-cardinality final union
therefore gives the optimum within this menu and budget.

Optimizing each output independently and then concatenating the results
would be wrong. With menu {1,2,3,4,5,16}, separate chosen minimum supports
for 5 and 16 can require five distinct writes in union. The joint optimum
is only four:

    1,2,4,5,16.

Incomparable supports must remain available until the joint requirements
are accounted for. State and support-pair resource budgets include the
additional join work. `ResourceLimit` means the search did not finish;
`None` means infeasibility only within the declared finite menu and budget.

Tests compare every menu through target 9 and every subset of its required
values with independent enumeration of increasing value sequences. They
also cover shared ancestors, duplicate/iterator requirements, unreachable
requirements, free initial 1, invalid and oversized requirements, and resource
stops during the joint stage. The generic finite-menu optimality proof remains
written; the fully formalized main claim is the concrete obstruction in
Sections 1–2.

## 6. Research context and next consequence

The AM level and defect convention is that of
[Tarek, Bahig and Anwar](https://doi.org/10.3934/Math.2026667).
Shared-intermediate synthesis is also studied in
[Arithmetic Expression Construction](https://arxiv.org/abs/2011.11767)
and [the 2026 multiple-constant-multiplication work](https://doi.org/10.4230/LIPIcs.CP.2026.11).
Their models do not supply this marked-root theorem or its lower bound;
expression trees, reusable DAGs and free hardware shifts must be distinguished.

The next root-sector reduction must ask which roots the actual continuation
needs and whether its growth conditions exclude costly retention patterns.
It cannot assume blanket root enrichment. This result records that failed
strengthening explicitly so it cannot silently become a hypothesis in a
later proof.
