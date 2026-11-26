# Squaring need not add an AM instruction

**Status: exact finite result, with a complete Lean formalization of the counterexample stated below.** Independent mathematical review and publication-priority review remain pending. The auxiliary search for the least exception and finite power census have executable certificates; their full range is not claimed as formally verified.

## Model and statement

An addition–multiplication chain starts at 1, strictly increases, and produces each new term by adding or multiplying any two earlier terms, including the same term twice. Each new term costs one instruction and all previous terms may be reused. Let ℓ(n) denote the minimum instruction count, and let λ(n)=floor(log₂ log₂ n)+1 for n≥2. Write δ(n)=ℓ(n)−λ(n).

**Theorem.** ℓ(267)=ℓ(267²)=8, where 267²=71,289. Consequently the proposed universal identity ℓ(n²)=ℓ(n)+1 is false. In defect notation, δ(267)=4 while δ(71,289)=3.

This tests a natural extension of the repository's [stability result through defect two](../seven-nonsquares/PROOF.md). We do not attribute that universal conjecture to the authors of the cited literature, and we make no novelty claim for the counterexample. [OEIS A230697](https://oeis.org/A230697/internal) already records the shortest-chain function, and [its table](https://oeis.org/A230697/b230697.txt) independently confirms ℓ(267)=8. The current AM-chain model is also the one used by [Tarek, Bahig and Anwar](https://doi.org/10.3934/Math.2026667).

## Upper bounds

Each row is one instruction. The initial 1 is free.

| Step | Construct 267 | Construct 71,289 |
|---:|---|---|
| 1 | 2=1+1 | 2=1+1 |
| 2 | 4=2×2 | 4=2×2 |
| 3 | 16=4×4 | 8=4+4 |
| 4 | 256=16×16 | 9=8+1 |
| 5 | 260=256+4 | 81=9×9 |
| 6 | 264=260+4 | 89=81+8 |
| 7 | 266=264+2 | 7,921=89×89 |
| 8 | 267=266+1 | 71,289=7,921×9 |

The squared construction uses 9 and 89 without ever constructing 3 or 267. The identity is 71,289=9×89²=(3×89)². A solver that insists on first producing the square root spends an unnecessary instruction on this target.

## Exhaustive lower bounds

Both seven-instruction impossibilities are checked by the Lean kernel. The verifier enumerates every next sum or product from the retained history, keeps increasing values at most the target, removes duplicate numerical choices, and explores each continuation. A proved growth bound prunes a branch only when its greatest possible future value is below the target. A separately proved final-step check tests the required sum or product directly.

The formal relation `Reach target k [1]` specifies a chain of exactly k writes. `search_complete` proves that every such chain is found by a search with any budget at least k. The two closed propositions `search 267 7 [1] = false` and `search 71289 7 [1] = false` are proved by kernel reduction using `decide`. There is no native-evaluation axiom, imported table, assumed search result or unproved pruning condition. Explicit `Reach` proofs supply the two upper bounds. `exact_pair` then proves both minima, and `no_universal_increment` disproves the universal extension. [Formal source](../../lean/SquareInstability.lean) · [Statement correspondence](FORMALIZATION.md).

A separate Python verifier uses two existing exact methods: iterative deepening by instruction count, and enumeration by small-step count. For 267, λ=4, so every chain of at most seven instructions has defect at most three. The second method enumerates 5, 43, 529 and 7,046 value sequences of defects zero through three below 267, with no endpoint 267. For 71,289, λ=5, so the relevant defect bound is two; it enumerates 6, 103 and 2,598 sequences, with no endpoint 71,289. These computations independently agree with the formal result.

## An infinite construction consequence

For every k≥1, append k−1 squares to the eight-write construction of 71,289. This produces 267^(2^k) in k+7 writes. Constructing 267 optimally and then squaring k times takes k+8 writes. Thus a one-instruction advantage over that particular strategy persists for an infinite family of targets. The Lean theorem `cheaper_power_family` formalizes this construction and strict cost comparison.

This does not assert that every member costs exactly k+7, or that infinitely many different bases exhibit a fresh defect drop. The exact finite census verifies the optimum k+7 for k=1,…,8. Its largest target has 2,064 bits. Any shorter chain for those targets would have defect at most two, and the complete bounded enumeration excludes it. Optimality for all larger powers remains open here.

## Least-exception check and limits

Iterative deepening over every n=2,…,267 finds no earlier exception. Hence this finite computation identifies 267 as the least positive nontrivial base with ℓ(n²)<ℓ(n)+1. This leastness statement is supported by the reproducible finite check, not included in the complete formalization claim. The special base 1 is excluded: it costs zero writes and is its own square.

The counterexample shows that the defect-at-most-three endpoint set is not closed under taking integral square roots. It does **not** settle whether every base of defect three remains stable when squared; that would require a drop from three to two. The earlier defect-two stability result is unchanged.

## Reproduce

```sh
python -m checks.verify_square_instability --least --powers
python -m unittest discover -s tests -p test_square_instability.py
python -m scripts.check_formalization
```

[Stored certificate](../../checks/expected/square-instability.json) · [Verifier](../../checks/verify_square_instability.py) · [Tests](../../tests/test_square_instability.py).
