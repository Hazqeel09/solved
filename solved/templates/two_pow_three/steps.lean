
theorem add_max_le' {F a b c : ℝ} (h1 : F + a ≤ c) (h2 : F + b ≤ c) : F + max a b ≤ c := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem Q3_zero (s t : ℝ) : Q3 0 s t = max (P0 0 s t) (P0 1 s t) := rfl
theorem Q3_one (s t : ℝ) : Q3 1 s t = V1 s t := rfl
theorem Q3_two (s t : ℝ) : Q3 2 s t = Q2 s t := rfl
theorem Q3_add3 (m : ℕ) (s t : ℝ) :
    Q3 (m + 3) s t = 10 / 3 * ((m + 3 : ℕ) : ℝ) + 46 / 9 + U3 ((-1 / 2 : ℝ) ^ (m + 3)) s t := rfl
theorem Q3_three (s t : ℝ) : Q3 3 s t = 10 + 46 / 9 + U3 (-1 / 8) s t := by
  rw [show (3 : ℕ) = 0 + 3 from rfl, Q3_add3]; norm_num

theorem step0 {s t z w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 0 ((s + z) / 2) ((t + w) / 2) ≤ Q3 1 s t := by
  rw [Q3_zero, Q3_one]
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact add_max_le' (up01_00_0 hs0 hs1 ht0 ht1) (up01_00_1 hs0 hs1 ht0 ht1)
  · exact add_max_le' (up01_01_0 hs0 hs1 ht0 ht1) (up01_01_1 hs0 hs1 ht0 ht1)
  · exact add_max_le' (up01_10_0 hs0 hs1 ht0 ht1) (up01_10_1 hs0 hs1 ht0 ht1)
  · exact add_max_le' (up01_11_0 hs0 hs1 ht0 ht1) (up01_11_1 hs0 hs1 ht0 ht1)

theorem step1 {s t z w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 1 ((s + z) / 2) ((t + w) / 2) ≤ Q3 2 s t := by
  rw [Q3_one, Q3_two, V1]
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact add_max_le' (add_max_le' (up12_00_0 hs0 hs1 ht0 ht1) (up12_00_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up12_00_2 hs0 hs1 ht0 ht1) (up12_00_3 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (up12_01_0 hs0 hs1 ht0 ht1) (up12_01_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up12_01_2 hs0 hs1 ht0 ht1) (up12_01_3 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (up12_10_0 hs0 hs1 ht0 ht1) (up12_10_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up12_10_2 hs0 hs1 ht0 ht1) (up12_10_3 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (up12_11_0 hs0 hs1 ht0 ht1) (up12_11_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up12_11_2 hs0 hs1 ht0 ht1) (up12_11_3 hs0 hs1 ht0 ht1))

theorem step2 {s t z w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 2 ((s + z) / 2) ((t + w) / 2) ≤ Q3 3 s t := by
  rw [Q3_two, Q3_three, Q2]
  rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
  · exact add_max_le' (add_max_le' (add_max_le' (up23_00_0 hs0 hs1 ht0 ht1) (up23_00_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up23_00_2 hs0 hs1 ht0 ht1) (up23_00_3 hs0 hs1 ht0 ht1))) (add_max_le' (up23_00_4 hs0 hs1 ht0 ht1) (up23_00_5 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (add_max_le' (up23_01_0 hs0 hs1 ht0 ht1) (up23_01_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up23_01_2 hs0 hs1 ht0 ht1) (up23_01_3 hs0 hs1 ht0 ht1))) (add_max_le' (up23_01_4 hs0 hs1 ht0 ht1) (up23_01_5 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (add_max_le' (up23_10_0 hs0 hs1 ht0 ht1) (up23_10_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up23_10_2 hs0 hs1 ht0 ht1) (up23_10_3 hs0 hs1 ht0 ht1))) (add_max_le' (up23_10_4 hs0 hs1 ht0 ht1) (up23_10_5 hs0 hs1 ht0 ht1))
  · exact add_max_le' (add_max_le' (add_max_le' (up23_11_0 hs0 hs1 ht0 ht1) (up23_11_1 hs0 hs1 ht0 ht1))
      (add_max_le' (up23_11_2 hs0 hs1 ht0 ht1) (up23_11_3 hs0 hs1 ht0 ht1))) (add_max_le' (up23_11_4 hs0 hs1 ht0 ht1) (up23_11_5 hs0 hs1 ht0 ht1))

theorem stepN {m : ℕ} {s t z w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 (m + 3) ((s + z) / 2) ((t + w) / 2) ≤
      Q3 (m + 3 + 1) s t := by
  obtain ⟨hρ0, hρ1⟩ := rho_bounds (n := m + 3) (by omega)
  have key : 2 * Fp 3 ((z - s) / 2) ((w - t) / 2) +
      U3 ((-1 / 2 : ℝ) ^ (m + 3)) ((s + z) / 2) ((t + w) / 2) ≤
      10 / 3 + U3 (-1 / 2 * (-1 / 2 : ℝ) ^ (m + 3)) s t := by
    unfold U3
    rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
    · exact add_max_le' (add_max_le' (stepU_00_0 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_00_1 hs0 hs1 ht0 ht1 hρ0 hρ1))
        (add_max_le' (stepU_00_2 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_00_3 hs0 hs1 ht0 ht1 hρ0 hρ1))
    · exact add_max_le' (add_max_le' (stepU_01_0 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_01_1 hs0 hs1 ht0 ht1 hρ0 hρ1))
        (add_max_le' (stepU_01_2 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_01_3 hs0 hs1 ht0 ht1 hρ0 hρ1))
    · exact add_max_le' (add_max_le' (stepU_10_0 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_10_1 hs0 hs1 ht0 ht1 hρ0 hρ1))
        (add_max_le' (stepU_10_2 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_10_3 hs0 hs1 ht0 ht1 hρ0 hρ1))
    · exact add_max_le' (add_max_le' (stepU_11_0 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_11_1 hs0 hs1 ht0 ht1 hρ0 hρ1))
        (add_max_le' (stepU_11_2 hs0 hs1 ht0 ht1 hρ0 hρ1) (stepU_11_3 hs0 hs1 ht0 ht1 hρ0 hρ1))
  rw [show m + 3 + 1 = (m + 1) + 3 by omega, Q3_add3, Q3_add3]
  rw [show (-1 / 2 : ℝ) ^ (m + 1 + 3) = -1 / 2 * (-1 / 2 : ℝ) ^ (m + 3) by ring]
  push_cast
  linarith

/-- The step from `n` to `n + 1`. -/
theorem Q3_step (n : ℕ) {s t z w : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1) :
    2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 n ((s + z) / 2) ((t + w) / 2) ≤ Q3 (n + 1) s t := by
  match n with
  | 0 => exact step0 hs0 hs1 ht0 ht1 hz hw
  | 1 => exact step1 hs0 hs1 ht0 ht1 hz hw
  | 2 => exact step2 hs0 hs1 ht0 ht1 hz hw
  | m + 3 => exact stepN hs0 hs1 ht0 ht1 hz hw
