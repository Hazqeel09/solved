import Formal.ICG.TwoPowChain

/-!
# Equality in the chain bound for `ICG(2^a P, S)`

The chain bound `chain_le` is an equality exactly when every step takes a *tight* choice:
`(z, w) = (1, 0)` on `Left` (the closed first branch of `Φ`) or `(0, 1)` on `Right`, and the
bottom choice is `(1, 0)`. `step_lt` and `base_lt` show that every other choice loses strictly;
`chain_tight` and `chain_ge_of_tight` turn this into a characterisation of equality.
-/
noncomputable section
namespace Solved.ICG.TwoPow

/-- Strictly on the first branch of `Φ`. -/
def SLeft (P s t : ℝ) : Prop := Aq P * s - Bq P * t - (Aq P - Bq P) < Bq P * t - Aq P * s

/-- Strictly on the second branch of `Φ`. -/
def SRight (P s t : ℝ) : Prop := Bq P * t - Aq P * s < Aq P * s - Bq P * t - (Aq P - Bq P)

set_option maxHeartbeats 40000000 in
theorem step_one_lt_00 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * Fp P ((0 - s) / 2) ((0 - t) / 2) < gq P + 2 / 3 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_half_lt_00 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * Fp P ((0 - s) / 2) ((0 - t) / 2) + 3 / 2 * Phi P ((s + 0) / 2) ((t + 0) / 2) <
      gq P - 1 / 3 + 3 / 4 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_one_lt_11 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * Fp P ((1 - s) / 2) ((1 - t) / 2) < gq P + 2 / 3 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_half_lt_11 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    2 * Fp P ((1 - s) / 2) ((1 - t) / 2) + 3 / 2 * Phi P ((s + 1) / 2) ((t + 1) / 2) <
      gq P - 1 / 3 + 3 / 4 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_one_lt_01 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SLeft P s t) :
    2 * Fp P ((0 - s) / 2) ((1 - t) / 2) < gq P + 2 / 3 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_half_lt_01 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SLeft P s t) :
    2 * Fp P ((0 - s) / 2) ((1 - t) / 2) + 3 / 2 * Phi P ((s + 0) / 2) ((t + 1) / 2) <
      gq P - 1 / 3 + 3 / 4 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_one_lt_10 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SRight P s t) :
    2 * Fp P ((1 - s) / 2) ((0 - t) / 2) < gq P + 2 / 3 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem step_half_lt_10 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SRight P s t) :
    2 * Fp P ((1 - s) / 2) ((0 - t) / 2) + 3 / 2 * Phi P ((s + 1) / 2) ((t + 0) / 2) <
      gq P - 1 / 3 + 3 / 4 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0000 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 0 0 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0001 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 0 0 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0010 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 0 1 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0011 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 0 1 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0100 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 1 0 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0101 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 1 0 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0110 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 1 1 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_0111 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 0 1 1 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1000 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 0 0 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1001 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SLeft P s t) :
    chain2 P s t 1 0 0 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1010 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hR : SRight P s t) :
    chain2 P s t 1 0 1 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1011 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 0 1 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1100 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 1 0 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1101 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 1 0 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1110 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 1 1 0 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith

set_option maxHeartbeats 40000000 in
theorem base_lt_1111 {P s t : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) :
    chain2 P s t 1 1 1 1 < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  have h1 := mul_nonneg (sub_nonneg.2 hP) hs0
  have h2 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 hs1)
  have h3 := mul_nonneg (sub_nonneg.2 hP) ht0
  have h4 := mul_nonneg (sub_nonneg.2 hP) (sub_nonneg.2 ht1)
  try unfold SLeft at hR
  try unfold SRight at hR
  try unfold chain2
  unfold Fp Phi Aq Bq gq at *
  try unfold Cq
  simp only [abs_eq_max_neg, max_def]
  split_ifs <;> linarith


theorem not_left_iff {P s t : ℝ} : ¬ Left P s t ↔ SRight P s t := by
  unfold Left SRight; exact not_le

theorem not_right_iff {P s t : ℝ} : ¬ Right P s t ↔ SLeft P s t := by
  unfold Right SLeft; exact not_le

/-- A tight choice at the state `(s, t)`. -/
def Tight (P s t z w : ℝ) : Prop := (z = 1 ∧ w = 0 ∧ Left P s t) ∨ (z = 0 ∧ w = 1 ∧ Right P s t)

/-- Every non-tight choice loses strictly. -/
theorem step_lt {P s t z w : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) (hT : ¬ Tight P s t z w) {n : ℕ}
    (hn : 1 ≤ n) :
    Fp P ((z - s) / 2) ((w - t) / 2) + Wb P n ((s + z) / 2) ((t + w) / 2) < Wb P (n + 1) s t := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  have key : 2 * Fp P ((z - s) / 2) ((w - t) / 2) < gq P + 2 / 3 + 3 / 2 * Phi P s t ∧
      2 * Fp P ((z - s) / 2) ((w - t) / 2) + 3 / 2 * Phi P ((s + z) / 2) ((t + w) / 2) <
        gq P - 1 / 3 + 3 / 4 * Phi P s t := by
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    · exact ⟨step_one_lt_00 hP hs0 hs1 ht0 ht1, step_half_lt_00 hP hs0 hs1 ht0 ht1⟩
    · have h := not_right_iff.1 fun h => hT (Or.inr ⟨rfl, rfl, h⟩)
      exact ⟨step_one_lt_01 hP hs0 hs1 ht0 ht1 h, step_half_lt_01 hP hs0 hs1 ht0 ht1 h⟩
    · have h := not_left_iff.1 fun h => hT (Or.inl ⟨rfl, rfl, h⟩)
      exact ⟨step_one_lt_10 hP hs0 hs1 ht0 ht1 h, step_half_lt_10 hP hs0 hs1 ht0 ht1 h⟩
    · exact ⟨step_one_lt_11 hP hs0 hs1 ht0 ht1, step_half_lt_11 hP hs0 hs1 ht0 ht1⟩
  obtain ⟨e1, e2⟩ := key
  obtain ⟨M, hM1, hM2, hM0⟩ : ∃ M : ℝ,
      M ≤ gq P + 2 / 3 + 3 / 2 * Phi P s t - 2 * Fp P ((z - s) / 2) ((w - t) / 2) ∧
      M ≤ gq P - 1 / 3 + 3 / 4 * Phi P s t -
        (2 * Fp P ((z - s) / 2) ((w - t) / 2) + 3 / 2 * Phi P ((s + z) / 2) ((t + w) / 2)) ∧
      0 < M := ⟨min _ _, min_le_left _ _, min_le_right _ _, lt_min (by linarith) (by linarith)⟩
  have ha : (0 : ℝ) ≤ (-1 / 2 : ℝ) ^ m + 1 / 2 := by linarith
  have hb : (0 : ℝ) ≤ 1 - (-1 / 2 : ℝ) ^ m := by linarith
  unfold Wb
  simp only [Nat.add_sub_cancel, pow_succ]
  push_cast
  nlinarith [mul_nonneg ha (sub_nonneg.2 hM1), mul_nonneg hb (sub_nonneg.2 hM2)]

/-- Every chain of length two whose choices are not tight with bottom `(1, 0)` loses strictly. -/
theorem base_lt {P s t z₀ w₀ z₁ w₁ : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz₀ : z₀ = 0 ∨ z₀ = 1) (hw₀ : w₀ = 0 ∨ w₀ = 1) (hz₁ : z₁ = 0 ∨ z₁ = 1)
    (hw₁ : w₁ = 0 ∨ w₁ = 1) (hT : ¬ (Tight P s t z₁ w₁ ∧ z₀ = 1 ∧ w₀ = 0)) :
    chain2 P s t z₀ w₀ z₁ w₁ < 2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P s t := by
  rcases hz₀ with rfl | rfl <;> rcases hw₀ with rfl | rfl <;> rcases hz₁ with rfl | rfl <;>
    rcases hw₁ with rfl | rfl
  exacts [base_lt_0000 hP hs0 hs1 ht0 ht1, base_lt_0001 hP hs0 hs1 ht0 ht1,
    base_lt_0010 hP hs0 hs1 ht0 ht1, base_lt_0011 hP hs0 hs1 ht0 ht1,
    base_lt_0100 hP hs0 hs1 ht0 ht1, base_lt_0101 hP hs0 hs1 ht0 ht1,
    base_lt_0110 hP hs0 hs1 ht0 ht1, base_lt_0111 hP hs0 hs1 ht0 ht1,
    base_lt_1000 hP hs0 hs1 ht0 ht1,
    base_lt_1001 hP hs0 hs1 ht0 ht1
      (not_right_iff.1 fun h => hT ⟨Or.inr ⟨rfl, rfl, h⟩, rfl, rfl⟩),
    base_lt_1010 hP hs0 hs1 ht0 ht1
      (not_left_iff.1 fun h => hT ⟨Or.inl ⟨rfl, rfl, h⟩, rfl, rfl⟩),
    base_lt_1011 hP hs0 hs1 ht0 ht1, base_lt_1100 hP hs0 hs1 ht0 ht1,
    base_lt_1101 hP hs0 hs1 ht0 ht1, base_lt_1110 hP hs0 hs1 ht0 ht1,
    base_lt_1111 hP hs0 hs1 ht0 ht1]

/-- A tight choice makes the step an equality. -/
theorem step_ge_of_tight {P s t z w : ℝ} (hP : 5 ≤ P) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hT : Tight P s t z w) {n : ℕ} (hn : 1 ≤ n) :
    Wb P (n + 1) s t ≤ Fp P ((z - s) / 2) ((w - t) / 2) + Wb P n ((s + z) / 2) ((t + w) / 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  have ha : (0 : ℝ) ≤ (-1 / 2 : ℝ) ^ m + 1 / 2 := by linarith
  have hb : (0 : ℝ) ≤ 1 - (-1 / 2 : ℝ) ^ m := by linarith
  rcases hT with ⟨rfl, rfl, hL⟩ | ⟨rfl, rfl, hR⟩
  · have e1 := step_one_ge_left hP hs0 hs1 ht0 ht1 hL
    have e2 := step_half_ge_left hP hs0 hs1 ht0 ht1 hL
    unfold Wb
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    nlinarith [mul_nonneg ha (sub_nonneg.2 e1), mul_nonneg hb (sub_nonneg.2 e2)]
  · have e1 := step_one_ge_right hP hs0 hs1 ht0 ht1 hR
    have e2 := step_half_ge_right hP hs0 hs1 ht0 ht1 hR
    unfold Wb
    simp only [Nat.add_sub_cancel, pow_succ]
    push_cast
    nlinarith [mul_nonneg ha (sub_nonneg.2 e1), mul_nonneg hb (sub_nonneg.2 e2)]

theorem state_bounds {σ z : ℕ → ℝ} {n : ℕ} (hz : z n = 0 ∨ z n = 1)
    (hσ : σ n = (σ (n + 1) + z n) / 2) (h0 : 0 ≤ σ (n + 1)) (h1 : σ (n + 1) ≤ 1) :
    0 ≤ σ n ∧ σ n ≤ 1 := by
  rw [hσ]; rcases hz with h | h <;> rw [h] <;> constructor <;> linarith

open Finset in
/-- **Equality in the chain bound.** The chain sum reaches `W_n` exactly when every choice above
the bottom is tight and the bottom choice is `(1, 0)`. -/
theorem chain_eq_iff {P : ℝ} (hP : 5 ≤ P) {σ τ z w : ℕ → ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hz : ∀ k < n, z k = 0 ∨ z k = 1) (hw : ∀ k < n, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < n, σ k = (σ (k + 1) + z k) / 2) (hτ : ∀ k < n, τ k = (τ (k + 1) + w k) / 2)
    (hs0 : 0 ≤ σ n) (hs1 : σ n ≤ 1) (ht0 : 0 ≤ τ n) (ht1 : τ n ≤ 1) :
    Wb P n (σ n) (τ n) ≤ Fp P (σ 0) (τ 0) + ∑ k ∈ range n, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1))
      ↔ (∀ k, 1 ≤ k → k < n → Tight P (σ (k + 1)) (τ (k + 1)) (z k) (w k)) ∧ z 0 = 1 ∧ w 0 = 0 := by
  induction n, hn using Nat.le_induction with
  | base =>
    have e1 := hσ 1 (by norm_num); have e0 := hσ 0 (by norm_num)
    have f1 := hτ 1 (by norm_num); have f0 := hτ 0 (by norm_num)
    have hsum : Fp P (σ 0) (τ 0) + ∑ k ∈ range 2, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) =
        chain2 P (σ 2) (τ 2) (z 0) (w 0) (z 1) (w 1) / 2 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, chain2]
      rw [show σ 1 - σ 2 = (z 1 - σ 2) / 2 by rw [e1]; ring,
        show τ 1 - τ 2 = (w 1 - τ 2) / 2 by rw [f1]; ring,
        show σ 0 - σ 1 = (z 0 - σ 1) / 2 by rw [e0]; ring,
        show τ 0 - τ 1 = (w 0 - τ 1) / 2 by rw [f0]; ring, e0, f0, e1, f1]
      ring
    have hW : Wb P 2 (σ 2) (τ 2) = (2 * gq P + Cq P + 2 / 9 + 3 / 2 * Phi P (σ 2) (τ 2)) / 2 := by
      unfold Wb; push_cast; norm_num
    rw [hsum, hW]
    have hk1 : ∀ k, 1 ≤ k → k < 2 → k = 1 := fun k h1 h2 => by omega
    constructor
    · intro h
      by_contra hne
      have hT : ¬ (Tight P (σ 2) (τ 2) (z 1) (w 1) ∧ z 0 = 1 ∧ w 0 = 0) := fun ⟨h1, h2⟩ =>
        hne ⟨fun k hk1' hk2 => by obtain rfl := hk1 k hk1' hk2; exact h1, h2⟩
      have := base_lt hP hs0 hs1 ht0 ht1 (hz 0 (by norm_num)) (hw 0 (by norm_num))
        (hz 1 (by norm_num)) (hw 1 (by norm_num)) hT
      linarith
    · rintro ⟨hT, h0, h0'⟩
      have hT1 := hT 1 le_rfl (by norm_num)
      rw [h0, h0']
      rcases hT1 with ⟨hz1, hw1, hL⟩ | ⟨hz1, hw1, hR⟩
      · rw [hz1, hw1]; have := base_ge_L hP hs0 hs1 ht0 ht1 hL; linarith
      · rw [hz1, hw1]; have := base_ge_R hP hs0 hs1 ht0 ht1 hR; linarith
  | succ n hn ih =>
    have hzn := hz n (by omega); have hwn := hw n (by omega)
    have en := hσ n (by omega); have fn := hτ n (by omega)
    obtain ⟨hs0', hs1'⟩ := state_bounds hzn en hs0 hs1
    obtain ⟨ht0', ht1'⟩ := state_bounds hwn fn ht0 ht1
    have ih' := ih (fun k hk => hz k (by omega)) (fun k hk => hw k (by omega))
      (fun k hk => hσ k (by omega)) (fun k hk => hτ k (by omega)) hs0' hs1' ht0' ht1'
    have hle := chain_le hP hn (fun k hk => hz k (by omega)) (fun k hk => hw k (by omega))
      (fun k hk => hσ k (by omega)) (fun k hk => hτ k (by omega)) hs0' hs1' ht0' ht1'
    have hterm : Fp P (σ n - σ (n + 1)) (τ n - τ (n + 1)) =
        Fp P ((z n - σ (n + 1)) / 2) ((w n - τ (n + 1)) / 2) := by
      rw [show σ n - σ (n + 1) = (z n - σ (n + 1)) / 2 by rw [en]; ring,
        show τ n - τ (n + 1) = (w n - τ (n + 1)) / 2 by rw [fn]; ring]
    have hnext : Wb P n (σ n) (τ n) = Wb P n ((σ (n + 1) + z n) / 2) ((τ (n + 1) + w n) / 2) := by
      rw [en, fn]
    rw [Finset.sum_range_succ, hterm]
    have hst := step hP hs0 hs1 ht0 ht1 hzn hwn (n := n) (by omega)
    constructor
    · intro h
      have htight : Tight P (σ (n + 1)) (τ (n + 1)) (z n) (w n) := by
        by_contra hne
        have := step_lt hP hs0 hs1 ht0 ht1 hzn hwn hne (n := n) (by omega)
        linarith
      obtain ⟨hT, h0⟩ := ih'.1 (by linarith)
      refine ⟨fun k hk1 hk2 => ?_, h0⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hk2 with hk | rfl
      · exact hT k hk1 hk
      · exact htight
    · rintro ⟨hT, h0⟩
      have hrest := ih'.2 ⟨fun k hk1 hk2 => hT k hk1 (by omega), h0⟩
      have hge := step_ge_of_tight hP hs0 hs1 ht0 ht1 (hT n (by omega) (by omega)) (n := n)
        (by omega)
      linarith

end Solved.ICG.TwoPow
