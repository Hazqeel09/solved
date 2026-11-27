# Formal statement correspondence

Each row of the table in [PROOF.md](PROOF.md) is one theorem in [`formal/Formal/ICG/MultiFamilies.lean`](../../formal/Formal/ICG/MultiFamilies.lean) (Lean 4.34.1, Mathlib v4.34.1).

| Mathematical object or step | Lean definition or theorem |
|---|---|
| $\mathrm{ICG}(n,S)$ and its energy (sum of absolute eigenvalues) | `ICGBridge.icgAdj n S`, `ICGBridge.energy` (H. Dong) |
| $S$ a set of proper divisors | `S ⊆ (n).properDivisors`, with `n` written out, e.g. `2 * p * q` |
| $p,q$ primes in the region | `hp : p.Prime`, `hq : q.Prime`, `hp0 : p₀ ≤ p`, `hpq : p < q` (or the mirror), and `p ≠ f`, `q ≠ f` for fixed primes `f ≥ p₀` |
| A row | `Solved.ICG.Multi.Families.energy_<order>_<lt|gt>` |
| Energy for $k$ distinct primes | `Solved.ICG.Multi.energy_icgAdj_multi` |
| Exponent vectors and their codes | `box`, `enc`, `dec`, `sum_box` (Mathlib's `finPiFinEquiv`) |
| Cell contributions on a region | `Shape`, `Shape.cellB`, `Shape.cast_eval_cellB` |
| The certificate and its soundness | `certifyM`, `certifyM_sound` (search `Solved.Cert.Packed.bnbP`, `bnbP_sound`) |
| From a certificate to graph energy | `energy_le_of_certifyM`, `energy_le_lt`, `energy_le_gt` |
| A successful check | `cert_<order>_<lt|gt>`, by `decide +kernel` |

**Trust.** Kernel reductions only, no `native_decide`; [`formal/FormalTests/Axioms.lean`](../../formal/FormalTests/Axioms.lean) fails the build unless each registered theorem depends exactly on the standard axioms, and `python -m scripts.check_catalogue` checks that the audit covers the theorems in [`docs/formalization-mathlib.json`](../../docs/formalization-mathlib.json).

**Outside this formalization.** $2p^2q$ and $2p^3q$ with $p>q$ (ratio-dependent maximisers), the orders of the companion entry with one symbolic prime and odd part $3^a$, any other order, and every claim about novelty or priority.
