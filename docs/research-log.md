# Research log

## 27 November 2026 — coverage and exclusion for the additive-gap argument

**Decision: improve the proof and its constructive consequences.** The bounded encoder already passed exact reconstruction tests, but its local coverage argument had only been written. The new [ChainCoverage module](../lean/ChainCoverage.lean) states the increasing AM-chain model explicitly and proves predecessor marking, nonsquare adjacency and square-run reconstruction for all chains in that model. The remaining normalization, count bound and finite-control packaging are still written arguments.

The [subtraction-gap module](../lean/SubtractionGap.lean) now checks the finite-family contradiction under a supplied coordinate-domination hypothesis. Encoding a bounded label alongside its complement forces two coordinatewise-comparable witnesses to share a label. This lets the formal argument handle finitely many controls and excesses without assuming one particular control occurs throughout the sequence.

The constructive consequence is an [upward-region certificate](../solved/square_exclusions.py). For one fixed control and excess, a checked endpoint at or below its associated tower-minus-one target excludes every strict increase of its square-run vector. The base itself is retained if it is an exact solution. Tests compare these exclusions with exact small integer evaluations, exercise incomparable vectors and other excesses, and check a coordinate of 10^100 without expanding the candidate.

**Quantitative direction needs a different argument.** A finite-control representation and Dickson's lemma do not supply a numerical last exception. [Controlled bad-sequence bounds](https://arxiv.org/abs/1007.2989) and [strongly monotone descending-chain bounds](https://doi.org/10.4230/LIPIcs.ICALP.2024.153) need hypotheses not established here. A complete effective enumeration must control remaining incomparable regions, not merely keep extending a known excluded vector. No gap-growth rate is claimed.

**Citation correction and related audit.** The AM-defect manuscript had linked Altman's addition-chain work to DOI `10.1016/j.tcs.2017.09.037`, which belongs to a different scheduling paper. It now links the [author's arXiv paper](https://arxiv.org/abs/1409.1627); Crossref identifies its journal DOI as `10.1016/j.tcs.2017.12.002`. The proof's mathematical dependencies did not use the incorrectly linked scheduling result.

The audit also checked the primary records for [Tarek–Bahig–Anwar's one-small-step paper](https://www.sciopen.com/article/10.3934/Math.2026667), [Cantaloube et al.'s MCM paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol379-cp2026/html/LIPIcs.CP.2026.11/LIPIcs.CP.2026.11.html), [Lee–Lee–Yi's synthesis paper](https://doi.org/10.1145/3776694), [Sethi's register paper](https://epubs.siam.org/doi/abs/10.1137/0204020), and [Bilardi–De Stefani's DAG-visit paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol250-fsttcs2022/LIPIcs.FSTTCS.2022.7/LIPIcs.FSTTCS.2022.7.pdf). Their identities match the citations. The two IJCAI references now use working publisher URLs: [binary threshold clauses](https://ijcai.org/proceedings/2009/78) and [connected row-convex constraints](https://ijcai.org/proceedings/2007/0029.pdf). Metadata failures and rate limits were not treated as evidence that a paper is absent.

All main statement review statuses remain unchanged. The new formal results certify their stated lemmas and hypotheses, not an end-to-end formal proof of the asymptotic separation.

## 27 November 2026 — squaring instability

**Decision: revamp the proposed universal squaring-stability extension.** The first broader defect census found 267²=71,289 in eight writes while 267 needs eight itself. The previous two-defect theorem remains valid, but global stability is false. Iterative deepening over every base from 2 through 267 found no smaller exception. The existing independent defect-bounded enumerator also excludes every seven-write chain for both targets.

The mathematical mechanism is the use of 9=3² and 89: 9×89² can be cheaper than first constructing 3×89 and squaring it. The squared witness retains 8 while building 9 and 81, allowing 89=81+8. This is a reason to retain different construction histories for a root and its powers.

A new Lean development gives an explicit increasing-AM reachability relation, proves completeness of a bounded all-pairs search and its maximum-growth pruning, and checks both seven-write impossibilities by kernel reduction. Direct witnesses prove both eight-write upper bounds. This yields a complete proof of the stated counterexample, including the negation of universal one-write growth. The final-step shortcut has its own completeness proof; it reduces kernel verification work without changing the search coverage.

The construction saves one write over base-then-square for every later power on the same ray. Exact minimum costs were additionally certified through eight squarings by excluding all two-defect competitors; optimality for every later power is not claimed. The least-exception and finite power censuses remain executable evidence beyond the formal statement. [Manuscript](../results/square-instability/PROOF.md) · [Formal correspondence](../results/square-instability/FORMALIZATION.md).

The [OEIS shortest AM-chain table](https://oeis.org/A230697/b230697.txt) independently records the cost of 267. Related entries A383001 and A383002 concern minimum values by chain length and counts by length, respectively; they are not squaring-stability statements. We do not claim the counterexample is previously unpublished.

A proposed prime-support shortcut was rejected: 89 already divides a two-small-step endpoint. The chain 1,2,3,9,81,729,531441,282429536481,79766443076872509863361,79766443076872509863442 reaches 3^48+81 in nine writes at level seven. Therefore the presence of a factor 89 alone cannot exclude the defect-at-most-two class. Any stronger lower bound must account for the full factor structure.
