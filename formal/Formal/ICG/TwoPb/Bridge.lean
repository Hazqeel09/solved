import Formal.ICG.TwoPowGraph

/-!
# The energy of `ICG(2 P^b, S)` as a chain along the `P`-adic path

Dong's two-prime bridge `energy_icgAdj_pq` with the primes in the order `(P, 2)` writes the energy of
`ICG(P^b 2, S)` as `L1mat P 2 b 1 Y` for the indicator `Y c e = [P^c 2^e ∈ S]`. Along the `P`-path
(`L1mat_path`) the inner factor is `‖T_1(2) v‖₁ = F₂(v₀, v₁)` with
`F₂(α, β) = |β - α| + |α + β| = 2 max(|α|, |β|)` (`TwoPow.L1_one` at `x = 2`), so

`E(ICG(2 P^b, S)) = P^b (F₂(ζ₀) + ∑_{k<b} F₂(ζ_k - ζ_{k+1}))`,

where `ζ_k = (ζ_{k+1} + (P - 1) Y_k)/P` and `ζ_b = Y_b = (Y_{b0}, 0)`.
-/

noncomputable section

namespace Solved.ICG.TwoPb

open Finset ICGGeneral Solved.ICG.TwoPow

/-- `F₂(α, β) = |β - α| + |α + β|`, the `ℓ¹` norm of `T_1(2) (α, β)`. -/
def F2 (α β : ℝ) : ℝ := |β - α| + |α + β|

theorem F2_eq (α β : ℝ) : F2 α β = 2 * max |α| |β| := by
  unfold F2
  rcases le_total 0 α with ha | ha <;> rcases le_total 0 β with hb | hb <;>
  · simp only [abs_eq_max_neg, max_def]
    split_ifs <;> linarith

theorem Fp_two (α β : ℝ) : Fp 2 α β = F2 α β := by
  unfold Fp F2; norm_num

/-- The indicator matrix of `S` on the exponent box of `P^b 2`: `Yp c e = [P^c 2^e ∈ S]`. -/
def Yp (P : ℕ) (S : Finset ℕ) (c e : ℕ) : ℝ := if P ^ c * 2 ^ e ∈ S then 1 else 0

theorem Yp_bit (P : ℕ) (S : Finset ℕ) (c e : ℕ) : Yp P S c e = 0 ∨ Yp P S c e = 1 := by
  unfold Yp; split_ifs <;> simp

/-- **The bridge.** -/
theorem energy_eq_chain (P b : ℕ) (hP : P.Prime) (hP2 : P ≠ 2) (S : Finset ℕ) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * P ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) =
      P ^ b * (F2 (zeta P b (Yp P S) 0 0) (zeta P b (Yp P S) 0 1) +
        ∑ k ∈ range b, F2 (zeta P b (Yp P S) k 0 - zeta P b (Yp P S) (k + 1) 0)
          (zeta P b (Yp P S) k 1 - zeta P b (Yp P S) (k + 1) 1)) := by
  have h := energy_icgAdj_pq P 2 b 1 hP Nat.prime_two hP2 S
  have hn : P ^ b * 2 ^ 1 = 2 * P ^ b := by ring
  rw [hn, Nat.cast_ofNat] at h
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP.pos
  rw [h, L1mat_path hP0]
  simp only [L1_one (by norm_num : (1 : ℝ) ≤ 2), Fp_two]
  rfl

theorem zeta_rec_p (P : ℕ) (hP : P.Prime) (S : Finset ℕ) {b : ℕ} (l : ℕ) {k : ℕ} (hk : k < b) :
    zeta P b (Yp P S) k l = (zeta P b (Yp P S) (k + 1) l + (P - 1) * Yp P S k l) / P :=
  zeta_rec (by exact_mod_cast hP.ne_zero) _ hk l

/-- The top cell `P^b 2 = n` is not a proper divisor. -/
theorem not_mem_top {P b : ℕ} {S : Finset ℕ} (hS : S ⊆ (2 * P ^ b).properDivisors) :
    Yp P S b 1 = 0 := by
  unfold Yp
  rw [ite_eq_right_iff]
  intro h
  have := hS h
  rw [pow_one, Nat.mem_properDivisors, mul_comm] at this
  exact absurd this.2 (lt_irrefl _)

end Solved.ICG.TwoPb
