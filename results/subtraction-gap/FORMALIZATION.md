# Formal statement correspondence

The main statement is that subtraction has an unbounded additive advantage on Nₙ=2^(2ⁿ)−1. The complete proof is checked by Lean 4.8.0. Independent expert review of the mathematical presentation and publication priority remains pending.

## Exact conclusion

`SolvedSeparation.eventual_additive_gap` proves:

```lean
∀ C : Nat, ∃ threshold, ∀ n, threshold ≤ n → ∀ a b,
  MinimumAM (2^(2^n)-1) a →
  MinimumSLP (2^(2^n)-1) b →
  b+C<a
```

`MinimumAM target a` characterizes the least number of addition/multiplication writes from 1. `MinimumSLP target b` characterizes the least number of integer addition/subtraction/multiplication writes from 1. Thus the statement means τ₊(Nₙ)−τ(Nₙ) tends to infinity. It asserts the bound for every sufficiently large member, not merely for an unspecified infinite subsequence.

`minima_exist` and `minima_unique` prove that the minimum relations exist and are unambiguous for every positive target. The final `unbounded_additive_advantage` theorem includes the existence of both minimum costs in its conclusion, so its claim is not made vacuous by unavailable programs.

## Arithmetic models

| Model | Exact formal meaning |
|---|---|
| AM program | `SolvedNormalization.Program r` has r writes, starts with the sole value 1, and uses only addition and multiplication of earlier results. Repeated values, identities, decreases relative to the preceding write and unused overshoots are allowed. |
| Increasing AM chain | `SolvedCoverage.Chain r` additionally requires strictly increasing values. Normalization from general AM programs is proved, not assumed. |
| Signed SLP | `SolvedSeparation.SignedProgram r` has integer-valued intermediates and operations `add`, `subtract`, `multiply`. Zero and negative intermediates are allowed. |
| Cost | Every primitive arithmetic write costs one. The initial 1 is free, and earlier results can be reused. There is no division, free constant 2 or free exponentiation operation. |
| Storage and size | The models have unrestricted retention and no magnitude cap. The theorem concerns arithmetic instruction count, not bit-operation runtime. |

Each program stores a value function together with earlier-operand indices and operations. The validity field constrains **every** write to the indicated arithmetic result; the value function cannot supply an arbitrary number as an oracle. Operand indices must precede the write, and the initial value is exactly 1.

The proof temporarily compresses successive squarings into marked blocks. A block representing k squarings has cost k. The extraction theorem preserves the original primitive instruction count exactly; compression does not introduce unit-cost powering.

## Checked dependency chain

| Mathematical step | Formal theorem |
|---|---|
| First write and canonical nonsquare counting | `SolvedGrowth.first_two`, `counted_canonical` |
| Integer Fibonacci growth envelope | `SolvedGrowth.envelope`, `fib_power_bound` |
| Bounded nonsquare count at fixed excess | `SolvedGrowth.mersenne_nonsquare_bound` |
| Complete marked-code extraction with exact cost and endpoint | `SolvedEncoding.complete_encoding`, `mersenne_encoding` |
| Ordered square-run parameters and exact cost comparison | `SolvedInflation.comparable_inflation`, `comparable_domination` |
| Incompatibility of two comparable Mersenne programs at the same excess | `SolvedSubtraction.mersenne_program_antichain` |
| Bounded control fields and complements force equal structure | `SolvedBounded.packed_comparison` |
| Finite-dimensional comparison | `SolvedControls.thin` |
| Eventual lower bound for every increasing AM chain | `SolvedBounded.eventual_chain_gap` |
| Normalization of arbitrary AM programs without increasing cost | `SolvedNormalization.normalize` |
| Eventual lower bound for arbitrary AM programs | `SolvedNormalization.eventual_program_gap` |
| Integer subtraction program of length n+2 | `SolvedSeparation.mersenneProgram_head` |
| Existence and uniqueness of minimum costs | `SolvedSeparation.minima_exist`, `minima_unique` |
| Full additive-gap statement | `SolvedSeparation.eventual_additive_gap`, `unbounded_additive_advantage` |

The main proof uses the integer count bound p≤4s+4. It does not assume the real-defect ordinal manuscripts, the all-length two-small-step classification, or any finite enumeration result. The finite-control construction, normalization and asymptotic argument are present in the checked source.

## Scope and trust

Run `python -m scripts.check_formalization` from a fresh checkout with the pinned Lean toolchain. The audit builds all modules and prints the axiom dependencies of every registered theorem. Only the standard Lean axioms `propext`, `Classical.choice` and `Quot.sound` are allowed. There are no project-specific axioms or unfinished proofs. The main argument does not use native evaluation as an additional proof oracle.

The result provides no effective cutoff or quantitative growth rate. It does not prove a superpolynomial separation; the cited paper already gives an AM construction of length at most 2n for this family. The other families, fixed-register variants and exact-division corollaries discussed in the manuscript remain outside this complete formalization. The alternative logarithmic count estimate p≤6s+2 is also outside the main formal dependency chain.

The Python model checks exercise arbitrary AM traces, normalization, negative signed intermediates and explicit tower programs. They support model interpretation but are not used to infer the unbounded conclusion.
