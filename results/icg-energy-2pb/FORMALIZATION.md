# Formal statement correspondence

The main claim of [PROOF.md](PROOF.md) is `Solved.ICG.TwoPb.energy_max_all` in
[`formal/Formal/ICG/TwoPb/Max.lean`](../../formal/Formal/ICG/TwoPb/Max.lean), in the Lean 4.34.1 / Mathlib project `formal/`.

| Mathematical object or step | Lean definition or theorem |
|---|---|
| The adjacency matrix of $\mathrm{ICG}(n,S)$, $A_{xy}=1$ iff $\gcd(y-x,n)\in S$, over `Fin n` | `ICGBridge.icgAdj n S` (H. Dong, ai4math-results) |
| Its energy, the sum of absolute eigenvalues (Mathlib's spectral theorem) | `ICGBridge.energy (ICGBridge.icgAdj n S) (ICGBridge.icgAdj_isHermitian _ _)` |
| $p$ an odd prime, $b\ge1$, $S$ a set of proper divisors of $2p^b$ | `hp : p.Prime`, `hp2 : p ≠ 2`, `hb : 1 ≤ b`, `S ⊆ (2 * p ^ b).properDivisors` |
| $2\sum_{j\le b}\varepsilon_j(b+1-j)p^{b-j}$, $\varepsilon_j=1,-1,-1,1$ | `Emax2pb p b`, `eps` ([`Sum.lean`](../../formal/Formal/ICG/TwoPb/Sum.lean)) |
| The maximiser $S^*$ | `setP p b (zOpt b) (wOpt b)` ([`Attain.lean`](../../formal/Formal/ICG/TwoPb/Attain.lean)), corners `cycZ`, `cycW` |
| Bound for every $S$ and equality at $S^*$, every $b\ge1$ | `energy_max_all`; $b\ge2$: `energy_max`, `energy_le` ([`Graph.lean`](../../formal/Formal/ICG/TwoPb/Graph.lean)); $b=1$: `Solved.ICG.Families.energy_1_1` |
| Energy as a chain along the $p$-adic path | `energy_eq_chain` ([`Bridge.lean`](../../formal/Formal/ICG/TwoPb/Bridge.lean)), from `ICGGeneral.energy_icgAdj_pq`, `L1mat_path`, `L1_one` |
| The scaled pieces $K Q_{k,i}$ in $y=p-3$, $\tau$, and their maxima | `Kc`, `Kg`, `Kgain`, `Qh_k_i`, `Mx_k`, `Mx_k_swap` ([`Pieces.lean`](../../formal/Formal/ICG/TwoPb/Pieces.lean), generated) |
| One step $T W_n\le W_{n+1}$ and the last step | `cand_*`, `base_*` (`Step*.lean`, `Base.lean`, generated); `step_k`, `base_any` (`Steps.lean`); `step_W`, `base_W` ([`Chain.lean`](../../formal/Formal/ICG/TwoPb/Chain.lean)) |
| The value bound $W_n$ and the chain induction | `Wh`, `tauN`, `chain_le` |
| The closed form of $S(b)$ and $p^bS(b)$ as a polynomial | `Ssum_closed`, `Ssum_eq_poly` |
| The start bound | `start_k`, `KS_k` (`Start.lean`, generated); `start_W` |
| Attainment along $S^*$ | `att_*` (`Start.lean`), `lower_step`, `lower_base`, `QL` (`AttainSteps.lean`, generated); `lower_chain`, `top_value` |
| Agreement with the certified families, $b\le7$ | `closed_form_eq_family` |

The generated modules come from `solved/lean_two_pb.py` and the untrusted data
`checks/expected/two-pb-certificates.json`; `python -m scripts.lean_icg_families --check` verifies they are current.
Each candidate lemma is proved by one `linear_combination` identity, `positivity` on polynomials in $y$, and the
elementary lemmas of [`Cert.lean`](../../formal/Formal/ICG/TwoPb/Cert.lean); there is no `native_decide`.
[`formal/FormalTests/Axioms.lean`](../../formal/FormalTests/Axioms.lean) fails the build unless the registered theorems
depend exactly on `propext`, `Classical.choice` and `Quot.sound`.

**Outside this formalization.** The complete list of maximisers (only one maximiser is stated), uniqueness, and every
claim about novelty or priority.
