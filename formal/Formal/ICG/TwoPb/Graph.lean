import Formal.ICG.TwoPb.Chain

/-!
# The maximal energy of `ICG(2 p^b, S)`: the upper bound

For every odd prime `p` and every `b ≥ 2`,
`E(ICG(2 p^b, S)) ≤ 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`, `ε = (1, -1, -1, 1)` repeating
(`energy_le`). The proof: the bridge (`energy_eq_chain`), the chain bound (`chain_le`) and the start
bound (`start_W`), with `y = p - 3`.
-/

noncomputable section

open Finset ICGGeneral

namespace Solved.ICG.TwoPb

theorem KS_0_eq {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) :
    KS_0 y τ = Kc y * (alphaS (1 / (y + 3)) + betaS (1 / (y + 3)) 0 * (1 / (y + 3)) ^ 4 * τ) := by
  have : y + 3 ≠ 0 := by positivity
  simp only [betaS]; norm_num
  unfold KS_0 Kc alphaS; field_simp; ring

theorem KS_1_eq {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) :
    KS_1 y τ = Kc y * (alphaS (1 / (y + 3)) + betaS (1 / (y + 3)) 1 * (1 / (y + 3)) ^ 1 * τ) := by
  have : y + 3 ≠ 0 := by positivity
  simp only [betaS]; norm_num
  unfold KS_1 Kc alphaS; field_simp; ring

theorem KS_2_eq {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) :
    KS_2 y τ = Kc y * (alphaS (1 / (y + 3)) + betaS (1 / (y + 3)) 2 * (1 / (y + 3)) ^ 2 * τ) := by
  have : y + 3 ≠ 0 := by positivity
  simp only [betaS]; norm_num
  unfold KS_2 Kc alphaS; field_simp; ring

theorem KS_3_eq {y : ℝ} (hy : 0 ≤ y) (τ : ℝ) :
    KS_3 y τ = Kc y * (alphaS (1 / (y + 3)) + betaS (1 / (y + 3)) 3 * (1 / (y + 3)) ^ 3 * τ) := by
  have : y + 3 ≠ 0 := by positivity
  simp only [betaS]; norm_num
  unfold KS_3 Kc alphaS; field_simp; ring

theorem betaS_mod (x : ℝ) (b : ℕ) : betaS x b = betaS x (b % 4) := by
  simp only [betaS, Nat.mod_mod]

/-- The value bound at the top state `(z, 0)` is `K S(b)` for `b ≥ 2`. -/
theorem start_W {y : ℝ} (hy : 0 ≤ y) {b : ℕ} (hb : 2 ≤ b) {z : ℝ} (hz : z = 0 ∨ z = 1) :
    Wh y b z 0 ≤ Kc y * Ssum (1 / (y + 3)) b := by
  have hx0 : (0 : ℝ) ≤ 1 / (y + 3) := by positivity
  have hxy : (y + 3) * (1 / (y + 3)) = 1 := by field_simp
  unfold Wh tauN mk
  rw [Ssum_closed, Kg_eq hy, betaS_mod]
  rcases mod4_cases b with h | h | h | h
  · rw [MxN_0 h, if_pos h, h]
    have hs := start_0 hy (by positivity) (pow_le_one₀ hx0 (x_le_one hy)) hz (τ := (1 / (y + 3)) ^ (b - 4))
    rw [KS_0_eq hy, mul_assoc, ← pow_add, show 4 + (b - 4) = b by omega] at hs
    push_cast; nlinarith [Kc_pos hy]
  · rw [MxN_1 h, if_neg (by omega), h]
    have hτ : (y + 3) ^ 4 * (1 / (y + 3)) ^ (b - 1) ≤ 1 := by
      rw [show b - 1 = 4 + (b - 5) by omega, pow_add, ← mul_assoc, ← mul_pow, hxy, one_pow, one_mul]
      exact pow_le_one₀ hx0 (x_le_one hy)
    have hs := start_1 hy (by positivity) hτ hz
    rw [KS_1_eq hy, mul_assoc, ← pow_add, show 1 + (b - 1) = b by omega] at hs
    push_cast; nlinarith [Kc_pos hy]
  · rw [MxN_2 h, if_neg (by omega), h]
    have hs := start_2 hy (by positivity) (pow_le_one₀ hx0 (x_le_one hy)) hz (τ := (1 / (y + 3)) ^ (b - 2))
    rw [KS_2_eq hy, mul_assoc, ← pow_add, show 2 + (b - 2) = b by omega] at hs
    push_cast; nlinarith [Kc_pos hy]
  · rw [MxN_3 h, if_neg (by omega), h]
    have hs := start_3 hy (by positivity) (pow_le_one₀ hx0 (x_le_one hy)) hz (τ := (1 / (y + 3)) ^ (b - 3))
    rw [KS_3_eq hy, mul_assoc, ← pow_add, show 3 + (b - 3) = b by omega] at hs
    push_cast; nlinarith [Kc_pos hy]

theorem three_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : (3 : ℝ) ≤ p := by
  have := hp.two_le
  have : 3 ≤ p := by omega
  exact_mod_cast this

/-- **Upper bound.** For every odd prime `p`, every `b ≥ 2` and every divisor set `S`,
`E(ICG(2 p^b, S)) ≤ 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`. -/
theorem energy_le {p b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 2 ≤ b) {S : Finset ℕ}
    (hS : S ⊆ (2 * p ^ b).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
      2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * (p : ℝ) ^ (b - j) := by
  have hp3 := three_le hp hp2
  set y : ℝ := (p : ℝ) - 3 with hydef
  have hy : 0 ≤ y := by linarith
  have hyp : y + 3 = p := by ring
  rw [energy_eq_chain p b hp hp2 S, ← Ssum_eq_poly (by positivity : (p : ℝ) ≠ 0)]
  have hrec : ∀ l, ∀ k < b, (y + 3) * zeta p b (Yp p S) k l =
      zeta p b (Yp p S) (k + 1) l + (y + 2) * Yp p S k l := by
    intro l k hk
    rw [zeta_rec_p p hp S l hk, hyp]
    field_simp
    ring
  have htop := not_mem_top hS
  have hc := chain_le hy (by omega : 1 ≤ b) (σ := fun k => zeta p b (Yp p S) k 0)
    (τ := fun k => zeta p b (Yp p S) k 1) (z := fun k => Yp p S k 0) (w := fun k => Yp p S k 1)
    (fun k _ => Yp_bit p S k 0) (fun k _ => Yp_bit p S k 1) (fun k hk => hrec 0 k hk)
    (fun k hk => hrec 1 k hk)
    (by simp only [zeta_last]; rcases Yp_bit p S b 0 with h | h <;> simp [h])
    (by simp only [zeta_last, htop]; norm_num)
  simp only [zeta_last, htop] at hc
  have hs := start_W hy hb (Yp_bit p S b 0)
  have hK := Kc_pos hy
  rw [hyp] at hs
  have hle : F2 (zeta p b (Yp p S) 0 0) (zeta p b (Yp p S) 0 1) +
      ∑ k ∈ range b, F2 (zeta p b (Yp p S) k 0 - zeta p b (Yp p S) (k + 1) 0)
        (zeta p b (Yp p S) k 1 - zeta p b (Yp p S) (k + 1) 1) ≤ Ssum (1 / (p : ℝ)) b :=
    le_of_mul_le_mul_left (hc.trans hs) hK
  exact mul_le_mul_of_nonneg_left hle (by positivity)

end Solved.ICG.TwoPb
