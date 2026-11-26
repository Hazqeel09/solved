# Formal statement correspondence

The main manuscript claim is that the minimum number of increasing addition–multiplication writes from 1 is eight for both 267 and 267², disproving universal one-write growth under squaring. The same file also formalizes the explicit infinite construction consequence.

| Mathematical object or step | Lean definition or theorem |
|---|---|
| Retained earlier values, newest first | `List Nat` history in `Reach` |
| A legal sum or product of any earlier pair | `Recipe` |
| Exactly k strictly increasing writes ending at n | `Reach n k [1]` |
| Minimum instruction cost | `Minimum` |
| Completeness of all-pairs next choices | `mem_options` |
| Every retained value is at most the current head | `HeadBound`, preserved by `cons_bound` |
| Valid maximum-growth pruning | `peak_mono`, `growth_mono`, `growth_steps`, `recipe_bound`, `reach_bound` |
| Complete last-step test | `oneStep_complete` |
| Every legal chain survives the bounded search | `search_complete` |
| No chain of length at most seven reaches either target | `no_seven_for_267`, `lower_267`, `no_seven_for_square`, `lower_square` |
| Explicit eight-write chains | `upper_267`, `upper_square` |
| ℓ(267)=ℓ(267²)=8 | `exact_pair` |
| Counterexample to universal one-write growth | `square_instability`, `no_universal_increment` |
| Eight-write squared construction followed by arbitrary further squares | `square_extension`, `upper_ray`, `cheaper_power_family` |

`Reach` uses natural numbers, starts from `[1]`, and permits only sums or products of retained values. Strict increase is a constructor premise. Positivity follows from the initial 1 and strict increase. Repeated operands are permitted. Storage is unrestricted. There is no subtraction, division, external seed, implicit square-root operation or unit-cost exponentiation in this model.

The search's target cap loses no chain: `head_le_target` derives it from the strictly increasing path ending at the target. Duplicate removal preserves membership by `mem_unique`. The formal lower bounds use only search completeness; the upper bounds are explicit relation proofs and do not depend on a separate search-soundness argument. The closed false results are ordinary kernel reductions, not `#eval` outputs or `native_decide` certificates. The repository's axiom audit covers every theorem in the file.

The full formalization claim excludes the separate least-exception search over 2–266 and the optimality census through eight squarings. It also excludes a model with nonmonotone, negative, subtractive or division steps. No claim that the example was previously unknown is formalized or inferred.
