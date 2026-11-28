import Mathlib

/-!
# A value function for the energy chain of `ICG(2^a P, S)`

For a real `P ≥ 5` let `F(α, β) = (P - 1)|β - α| + |(P - 1)α + β|`; this is `‖T_1(P) (α, β)‖₁`
(`formal/Formal/ICG/TwoPowGraph.lean`). Along the `2`-adic path of the bridge, the energy of
`ICG(2^a P, S)` is `2^a (F(σ₀, τ₀) + ∑_{k<a} F(σ_k - σ_{k+1}, τ_k - τ_{k+1}))`, where
`σ_k = (σ_{k+1} + z_k)/2` and `τ_k = (τ_{k+1} + w_k)/2` for the indicator bits `z_k, w_k` of
`2^k, 2^k P ∈ S`.

`chain_le` bounds this sum by an explicit value function
`W_n(s, t) = (n g + C + (8/9)(-1/2)^n + (1 - (-1/2)^(n-1)) Φ(s, t)) / 2` of the top state, with
`g = 2P - 8/3`, `C = 2P - 8/9` and the piecewise linear potential
`Φ(s, t) = max(B t - A s, A s - B t - (A - B))`, `A = 4(P-1)/3`, `B = 2(P-2)/3`. The proof is
induction on the chain length from `n = 2`: one step is the inequality `step` (affine in
`μ = (-1/2)^(n-1) ∈ [-1/2, 1]`, so it reduces to the endpoints `step_one`, `step_half`), and the
base is `base_two`. All three are piecewise linear inequalities in `s, t` with coefficients
affine in `P`, proved by case analysis.
-/

noncomputable section

namespace Solved.ICG.TwoPow

/-- `F(α, β) = (P - 1)|β - α| + |(P - 1)α + β|`. -/
def Fp (P α β : ℝ) : ℝ := (P - 1) * |β - α| + |(P - 1) * α + β|

/-- `A = 4(P - 1)/3`. -/
def Aq (P : ℝ) : ℝ := 4 * (P - 1) / 3

/-- `B = 2(P - 2)/3`. -/
def Bq (P : ℝ) : ℝ := 2 * (P - 2) / 3

/-- The potential `Φ(s, t) = max(B t - A s, A s - B t - (A - B))`. -/
def Phi (P s t : ℝ) : ℝ := max (Bq P * t - Aq P * s) (Aq P * s - Bq P * t - (Aq P - Bq P))

/-- The gain per level, `g = 2P - 8/3`. -/
def gq (P : ℝ) : ℝ := 2 * P - 8 / 3

/-- The constant `C = 2P - 8/9`. -/
def Cq (P : ℝ) : ℝ := 2 * P - 8 / 9

/-- The value function `W_n(s, t)` (in units of `F`). -/
def Wb (P : ℝ) (n : ℕ) (s t : ℝ) : ℝ :=
  (n * gq P + Cq P + 8 / 9 * (-1 / 2 : ℝ) ^ n + (1 - (-1 / 2 : ℝ) ^ (n - 1)) * Phi P s t) / 2

set_option maxHeartbeats 4000000 in
/-- The step at `μ = 1`. -/
theorem step_one {P s t z w : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp P ((z - s) / 2) ((w - t) / 2) ≤ gq P + 2 / 3 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Fp Phi Aq Bq gq
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
  · simp only [abs_eq_max_neg, max_def]
    split_ifs <;> nlinarith

set_option maxHeartbeats 4000000 in
/-- The step at `μ = -1/2`. -/
theorem step_half {P s t z w : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp P ((z - s) / 2) ((w - t) / 2) + 3 / 2 * Phi P ((s + z) / 2) ((t + w) / 2) ≤
      gq P - 1 / 3 + 3 / 4 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Fp Phi Aq Bq gq
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl <;>
  · simp only [abs_eq_max_neg, max_def]
    split_ifs <;> nlinarith

theorem neg_half_pow_bounds (m : ℕ) : -1 / 2 ≤ (-1 / 2 : ℝ) ^ m ∧ (-1 / 2 : ℝ) ^ m ≤ 1 := by
  have h : |(-1 / 2 : ℝ) ^ m| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (by norm_num) (by norm_num [abs_div])
  rcases m with _ | m
  · norm_num
  · refine ⟨?_, (abs_le.1 h).2⟩
    have h' : |(-1 / 2 : ℝ) ^ m| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (by norm_num) (by norm_num [abs_div])
    rw [pow_succ]; nlinarith [abs_le.1 h']

/-- One step of the chain: `F` of the new increment plus `W_n` of the next state is at most
`W_{n+1}` of the current state. -/
theorem step {P s t z w : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) {n : ℕ} (hn : 1 ≤ n) :
    Fp P ((z - s) / 2) ((w - t) / 2) + Wb P n ((s + z) / 2) ((t + w) / 2) ≤ Wb P (n + 1) s t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 := step_one hP hs0 hs1 ht0 ht1 hz hw
  have e2 := step_half hP hs0 hs1 ht0 ht1 hz hw
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  unfold Wb
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (-1 / 2 : ℝ) ^ m + 1 / 2) (sub_nonneg.2 e1),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (-1 / 2 : ℝ) ^ m) (sub_nonneg.2 e2)]

/-! ## The base case `n = 2` -/

/-- Twice the chain sum of length two below the top state `(s, t)`. -/
def chain2 (P s t z₀ w₀ z₁ w₁ : ℝ) : ℝ :=
  2 * (Fp P (((s + z₁) / 2 + z₀) / 2) (((t + w₁) / 2 + w₀) / 2) +
    Fp P ((z₀ - (s + z₁) / 2) / 2) ((w₀ - (t + w₁) / 2) / 2) + Fp P ((z₁ - s) / 2) ((w₁ - t) / 2))

set_option maxHeartbeats 40000000 in
theorem base_0000 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 0 0 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0001 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 0 0 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0010 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 0 1 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0011 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 0 1 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0100 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 1 0 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0101 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 1 0 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0110 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 1 1 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_0111 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 0 1 1 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1000 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 0 0 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1001 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 0 0 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1010 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 0 1 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1011 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 0 1 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1100 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 1 0 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1101 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 1 0 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1110 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 1 1 0 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_1111 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : chain2 P s t 1 1 1 1 ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold chain2 Fp Phi Aq Bq gq Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

/-- The base case: every chain of length two is at most `2 W_2`. -/
theorem base_two {P s t z₀ w₀ z₁ w₁ : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz₀ : z₀ = 0 ∨ z₀ = 1) (hw₀ : w₀ = 0 ∨ w₀ = 1) (hz₁ : z₁ = 0 ∨ z₁ = 1)
    (hw₁ : w₁ = 0 ∨ w₁ = 1) :
    chain2 P s t z₀ w₀ z₁ w₁ ≤ 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  rcases hz₀ with rfl | rfl <;> rcases hw₀ with rfl | rfl <;> rcases hz₁ with rfl | rfl <;>
    rcases hw₁ with rfl | rfl
  exacts [base_0000 hP hs0 hs1 ht0 ht1, base_0001 hP hs0 hs1 ht0 ht1, base_0010 hP hs0 hs1 ht0 ht1,
    base_0011 hP hs0 hs1 ht0 ht1, base_0100 hP hs0 hs1 ht0 ht1, base_0101 hP hs0 hs1 ht0 ht1,
    base_0110 hP hs0 hs1 ht0 ht1, base_0111 hP hs0 hs1 ht0 ht1, base_1000 hP hs0 hs1 ht0 ht1,
    base_1001 hP hs0 hs1 ht0 ht1, base_1010 hP hs0 hs1 ht0 ht1, base_1011 hP hs0 hs1 ht0 ht1,
    base_1100 hP hs0 hs1 ht0 ht1, base_1101 hP hs0 hs1 ht0 ht1, base_1110 hP hs0 hs1 ht0 ht1,
    base_1111 hP hs0 hs1 ht0 ht1]

/-! ## The chain bound -/

open Finset in
/-- **The chain bound.** For bits `z, w ∈ {0,1}` and states with `σ_k = (σ_{k+1} + z_k)/2`,
`τ_k = (τ_{k+1} + w_k)/2` below a top state in `[0,1]²`, the chain sum is at most `W_n`. -/
theorem chain_le {P : ℝ} (hP : 5 ≤ P) {σ τ z w : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hz : ∀ k < n, z k = 0 ∨ z k = 1) (hw : ∀ k < n, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < n, σ k = (σ (k + 1) + z k) / 2) (hτ : ∀ k < n, τ k = (τ (k + 1) + w k) / 2)
    (hs0 : 0 ≤ σ n) (hs1 : σ n ≤ 1) (ht0 : 0 ≤ τ n) (ht1 : τ n ≤ 1) :
    Fp P (σ 0) (τ 0) + ∑ k ∈ range n, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) ≤
      Wb P n (σ n) (τ n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    have e1 := hσ 1 (by norm_num); have e0 := hσ 0 (by norm_num)
    have f1 := hτ 1 (by norm_num); have f0 := hτ 0 (by norm_num)
    have hb := base_two hP hs0 hs1 ht0 ht1 (hz 0 (by norm_num)) (hw 0 (by norm_num))
      (hz 1 (by norm_num)) (hw 1 (by norm_num))
    unfold chain2 at hb
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [show σ 1 - σ 2 = (z 1 - σ 2) / 2 by rw [e1]; ring,
      show τ 1 - τ 2 = (w 1 - τ 2) / 2 by rw [f1]; ring,
      show σ 0 - σ 1 = (z 0 - σ 1) / 2 by rw [e0]; ring,
      show τ 0 - τ 1 = (w 0 - τ 1) / 2 by rw [f0]; ring, e0, f0, e1, f1]
    unfold Wb; push_cast; norm_num; linarith
  | succ n hn ih =>
    have hzn := hz n (by omega); have hwn := hw n (by omega)
    have en := hσ n (by omega); have fn := hτ n (by omega)
    have hs0' : 0 ≤ σ n := by rw [en]; rcases hzn with h | h <;> rw [h] <;> linarith
    have hs1' : σ n ≤ 1 := by rw [en]; rcases hzn with h | h <;> rw [h] <;> linarith
    have ht0' : 0 ≤ τ n := by rw [fn]; rcases hwn with h | h <;> rw [h] <;> linarith
    have ht1' : τ n ≤ 1 := by rw [fn]; rcases hwn with h | h <;> rw [h] <;> linarith
    have ih' := ih (fun k hk => hz k (by omega)) (fun k hk => hw k (by omega))
      (fun k hk => hσ k (by omega)) (fun k hk => hτ k (by omega)) hs0' hs1' ht0' ht1'
    have hst := step hP hs0 hs1 ht0 ht1 hzn hwn (n := n) (by omega)
    rw [Finset.sum_range_succ,
      show σ n - σ (n + 1) = (z n - σ (n + 1)) / 2 by rw [en]; ring,
      show τ n - τ (n + 1) = (w n - τ (n + 1)) / 2 by rw [fn]; ring]
    rw [en, fn] at ih'
    linarith

/-- At the top state `(z, 0)` with `z ∈ {0, 1}`, `2^a W_a` is at most the closed form
`c_a P - d_a`, with equality for `z = 1`. -/
theorem Wb_top {P : ℝ} (hP : 5 ≤ P) {a : ℕ} (ha : 1 ≤ a) {z : ℝ} (hz : z = 0 ∨ z = 1) :
    2 ^ a * Wb P a z 0 ≤ 2 ^ a * Wb P a 1 0 ∧
    2 ^ a * Wb P a 1 0 = (2 ^ a * (3 * a + 4) + 2 * (-1) ^ a) * P / 3 -
      (2 ^ a * (12 * a + 10) + 8 * (-1) ^ a) / 9 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 1 := ⟨a - 1, by omega⟩
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  have hpow : (2 : ℝ) ^ m * (-1 / 2) ^ m = (-1) ^ m := by rw [← mul_pow]; norm_num
  have hΦ1 : Phi P 1 0 = Bq P := by
    unfold Phi Aq Bq; rw [max_eq_right (by nlinarith)]; ring
  have hΦ0 : Phi P 0 0 ≤ Bq P := by unfold Phi Aq Bq; apply max_le <;> nlinarith
  have hΦ : Phi P z 0 ≤ Phi P 1 0 := by rcases hz with rfl | rfl; exacts [hΦ1 ▸ hΦ0, le_rfl]
  refine ⟨?_, ?_⟩
  · unfold Wb
    have hc : 0 ≤ 1 - (-1 / 2 : ℝ) ^ (m + 1 - 1) := by simp only [Nat.add_sub_cancel]; linarith
    have := mul_le_mul_of_nonneg_left hΦ hc
    have h2 : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    nlinarith
  · unfold Wb
    rw [hΦ1]
    simp only [Nat.add_sub_cancel, pow_succ]
    unfold Bq gq Cq
    push_cast
    linear_combination (-4 / 9 - 2 * (P - 2) / 3) * hpow

/-! ## Attainment -/

/-- Region of the first branch of `Φ`. -/
def Left (P s t : ℝ) : Prop := Aq P * s - Bq P * t - (Aq P - Bq P) ≤ Bq P * t - Aq P * s

set_option maxHeartbeats 4000000 in
theorem step_one_ge_left {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hL : Left P s t) :
    gq P + 2 / 3 + 3 / 2 * Phi P s t ≤ 2 * Fp P ((1 - s) / 2) ((0 - t) / 2) := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at hL
  unfold Fp Phi Aq Bq gq at *
  rw [max_eq_left hL]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 4000000 in
theorem step_half_ge_left {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hL : Left P s t) :
    gq P - 1 / 3 + 3 / 4 * Phi P s t ≤
      2 * Fp P ((1 - s) / 2) ((0 - t) / 2) + 3 / 2 * Phi P ((s + 1) / 2) ((t + 0) / 2) := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at hL
  unfold Fp Phi Aq Bq gq at *
  rw [max_eq_left hL]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 4000000 in
theorem step_one_ge_right {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : ¬ Left P s t) :
    gq P + 2 / 3 + 3 / 2 * Phi P s t ≤ 2 * Fp P ((0 - s) / 2) ((1 - t) / 2) := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at hR
  push Not at hR
  unfold Fp Phi Aq Bq gq at *
  rw [max_eq_right hR.le]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> first | linarith | nlinarith

set_option maxHeartbeats 4000000 in
theorem step_half_ge_right {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : ¬ Left P s t) :
    gq P - 1 / 3 + 3 / 4 * Phi P s t ≤
      2 * Fp P ((0 - s) / 2) ((1 - t) / 2) + 3 / 2 * Phi P ((s + 0) / 2) ((t + 1) / 2) := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at hR
  push Not at hR
  unfold Fp Phi Aq Bq gq at *
  rw [max_eq_right hR.le]
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> first | linarith | nlinarith

set_option maxHeartbeats 40000000 in
theorem base_ge_L {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (h1L : Left P s t) :
    2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t ≤ chain2 P s t 1 0 1 0 := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at h1L
  try push Not at h1L
  unfold chain2 Fp Phi Aq Bq gq Cq at *
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_ge_R {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (h1L : ¬ Left P s t) :
    2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t ≤ chain2 P s t 1 0 0 1 := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  unfold Left at h1L
  try push Not at h1L
  unfold chain2 Fp Phi Aq Bq gq Cq at *
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> first | linarith | nlinarith


/-- The step along the choice `(1, 0)` on `Left` and `(0, 1)` off it is an equality. -/
theorem step_ge {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) {n : ℕ} (hn : 1 ≤ n) :
    ∃ z w : ℝ, (z = 0 ∨ z = 1) ∧ (w = 0 ∨ w = 1) ∧
      Wb P (n + 1) s t ≤ Fp P ((z - s) / 2) ((w - t) / 2) + Wb P n ((s + z) / 2) ((t + w) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  by_cases hL : Left P s t
  · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
    have e1 := step_one_ge_left hP hs0 hs1 ht0 ht1 hL
    have e2 := step_half_ge_left hP hs0 hs1 ht0 ht1 hL
    unfold Wb
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (-1 / 2 : ℝ) ^ m + 1 / 2) (sub_nonneg.2 e1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (-1 / 2 : ℝ) ^ m) (sub_nonneg.2 e2)]
  · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
    have e1 := step_one_ge_right hP hs0 hs1 ht0 ht1 hL
    have e2 := step_half_ge_right hP hs0 hs1 ht0 ht1 hL
    unfold Wb
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ (-1 / 2 : ℝ) ^ m + 1 / 2) (sub_nonneg.2 e1),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - (-1 / 2 : ℝ) ^ m) (sub_nonneg.2 e2)]

open Finset in
/-- **Attainment.** Every top state in `[0,1]²` has bits whose chain sum equals `W_n`. -/
theorem chain_attain {P : ℝ} (hP : 5 ≤ P) {n : ℕ} (hn : 2 ≤ n) {s t : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ σ τ z w : ℕ → ℝ, (∀ k < n, z k = 0 ∨ z k = 1) ∧ (∀ k < n, w k = 0 ∨ w k = 1) ∧
      (∀ k < n, σ k = (σ (k + 1) + z k) / 2) ∧ (∀ k < n, τ k = (τ (k + 1) + w k) / 2) ∧
      σ n = s ∧ τ n = t ∧
      Wb P n s t ≤ Fp P (σ 0) (τ 0) + ∑ k ∈ range n, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) := by
  induction n, hn using Nat.le_induction generalizing s t with
  | base =>
    obtain ⟨z₁, w₁, hz₁, hw₁, hb⟩ : ∃ z₁ w₁ : ℝ, (z₁ = 0 ∨ z₁ = 1) ∧ (w₁ = 0 ∨ w₁ = 1) ∧
        2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t ≤ chain2 P s t 1 0 z₁ w₁ := by
      by_cases hL : Left P s t
      · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, base_ge_L hP hs0 hs1 ht0 ht1 hL⟩
      · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, base_ge_R hP hs0 hs1 ht0 ht1 hL⟩
    refine ⟨fun k => if k = 0 then ((s + z₁) / 2 + 1) / 2 else if k = 1 then (s + z₁) / 2 else s,
      fun k => if k = 0 then ((t + w₁) / 2 + 0) / 2 else if k = 1 then (t + w₁) / 2 else t,
      fun k => if k = 0 then 1 else z₁, fun k => if k = 0 then 0 else w₁, ?_, ?_, ?_, ?_,
      by simp, by simp, ?_⟩
    · intro k hk; interval_cases k <;> simp [hz₁]
    · intro k hk; interval_cases k <;> simp [hw₁]
    · intro k hk; interval_cases k <;> simp
    · intro k hk; interval_cases k <;> simp
    · unfold chain2 at hb
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      simp only [↓reduceIte, one_ne_zero]
      unfold Wb; push_cast; norm_num
      have e1 : (s + z₁) / 2 - s = (z₁ - s) / 2 := by ring
      have e2 : (t + w₁) / 2 - t = (w₁ - t) / 2 := by ring
      have e3 : ((s + z₁) / 2 + 1) / 2 - (s + z₁) / 2 = (1 - (s + z₁) / 2) / 2 := by ring
      have e4 : (t + w₁) / 2 / 2 - (t + w₁) / 2 = (0 - (t + w₁) / 2) / 2 := by ring
      rw [e1, e2, e3, e4]
      norm_num at hb ⊢
      linarith
  | succ n hn ih =>
    obtain ⟨z₀, w₀, hz₀, hw₀, hst⟩ := step_ge hP hs0 hs1 ht0 ht1 (n := n) (by omega)
    have hs0' : 0 ≤ (s + z₀) / 2 := by rcases hz₀ with h | h <;> rw [h] <;> linarith
    have hs1' : (s + z₀) / 2 ≤ 1 := by rcases hz₀ with h | h <;> rw [h] <;> linarith
    have ht0' : 0 ≤ (t + w₀) / 2 := by rcases hw₀ with h | h <;> rw [h] <;> linarith
    have ht1' : (t + w₀) / 2 ≤ 1 := by rcases hw₀ with h | h <;> rw [h] <;> linarith
    obtain ⟨σ, τ, z, w, hz, hw, hσ, hτ, hσn, hτn, hsum⟩ := ih hs0' hs1' ht0' ht1'
    refine ⟨Function.update σ (n + 1) s, Function.update τ (n + 1) t, Function.update z n z₀,
      Function.update w n w₀, ?_, ?_, ?_, ?_, by simp, by simp, ?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Function.update_of_ne hk.ne]; exact hz k hk
      · simpa using hz₀
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Function.update_of_ne hk.ne]; exact hw k hk
      · simpa using hw₀
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne hk.ne]
        exact hσ k hk
      · simp [hσn]
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk | rfl
      · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne hk.ne]
        exact hτ k hk
      · simp [hτn]
    · rw [Finset.sum_range_succ]
      have hk : ∀ k ∈ range n, Fp P (Function.update σ (n + 1) s k -
            Function.update σ (n + 1) s (k + 1))
          (Function.update τ (n + 1) t k - Function.update τ (n + 1) t (k + 1)) =
          Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) := by
        intro k hk
        have hk' := Finset.mem_range.1 hk
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
          Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      have a1 : Function.update σ (n + 1) s 0 = σ 0 := Function.update_of_ne (by omega) _ _
      have a2 : Function.update τ (n + 1) t 0 = τ 0 := Function.update_of_ne (by omega) _ _
      have a3 : Function.update σ (n + 1) s n = σ n := Function.update_of_ne (by omega) _ _
      have a4 : Function.update τ (n + 1) t n = τ n := Function.update_of_ne (by omega) _ _
      rw [Finset.sum_congr rfl hk, a1, a2, a3, a4, Function.update_self, Function.update_self,
        hσn, hτn]
      have : Fp P ((s + z₀) / 2 - s) ((t + w₀) / 2 - t) = Fp P ((z₀ - s) / 2) ((w₀ - t) / 2) := by
        congr 1 <;> ring
      rw [this]
      linarith

end Solved.ICG.TwoPow
