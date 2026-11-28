
/-! ## Assembly -/

theorem Tp_affine (j : ℕ) (ρ s t : ℝ) : Tp j ρ s t = Tp j 0 s t + ρ * (Tp j 1 s t - Tp j 0 s t) := by
  rcases j with _ | _ | _ | j <;> simp only [Tp] <;> ring

theorem slk_mid {z w : ℝ} {i j : ℕ} {ρ s t : ℝ} (hρ0 : -1 / 8 ≤ ρ) (hρ1 : ρ ≤ 1 / 16)
    (hlo : 0 ≤ slk z w i j (-1 / 8) s t) (hhi : 0 ≤ slk z w i j (1 / 16) s t) :
    0 ≤ slk z w i j ρ s t := by
  have e : slk z w i j ρ s t * (1 / 16 - -1 / 8) =
      (1 / 16 - ρ) * slk z w i j (-1 / 8) s t + (ρ - -1 / 8) * slk z w i j (1 / 16) s t := by
    unfold slk; rw [Tp_affine j, Tp_affine i, Tp_affine j (-1 / 2 * (-1 / 8)), Tp_affine i (-1 / 8),
      Tp_affine j (-1 / 2 * (1 / 16)), Tp_affine i (1 / 16)]; ring
  nlinarith [mul_nonneg (sub_nonneg.2 hρ1) hlo, mul_nonneg (by linarith : (0 : ℝ) ≤ ρ - -1 / 8) hhi]

theorem slkA_mid {z w : ℝ} {i k : ℕ} {ρ s t : ℝ} (hρ0 : -1 / 8 ≤ ρ) (hρ1 : ρ ≤ 1 / 16)
    (hlo : 0 ≤ slkA z w i k (-1 / 8) s t) (hhi : 0 ≤ slkA z w i k (1 / 16) s t) :
    0 ≤ slkA z w i k ρ s t := by
  have e : slkA z w i k ρ s t * (1 / 16 - -1 / 8) =
      (1 / 16 - ρ) * slkA z w i k (-1 / 8) s t + (ρ - -1 / 8) * slkA z w i k (1 / 16) s t := by
    unfold slkA; rw [Tp_affine k, Tp_affine i, Tp_affine k (-1 / 8), Tp_affine i (-1 / 2 * (-1 / 8)),
      Tp_affine k (1 / 16), Tp_affine i (-1 / 2 * (1 / 16))]; ring
  nlinarith [mul_nonneg (sub_nonneg.2 hρ1) hlo, mul_nonneg (by linarith : (0 : ℝ) ≤ ρ - -1 / 8) hhi]

theorem Tp_le_U3 {j : ℕ} (hj : j ≤ 3) (ρ s t : ℝ) : Tp j ρ s t ≤ U3 ρ s t := by
  unfold U3
  interval_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem U3_piece (ρ s t : ℝ) : ∃ j ≤ 3, U3 ρ s t = Tp j ρ s t := by
  unfold U3
  rcases max_choice (Tp 0 ρ s t) (Tp 1 ρ s t) with h1 | h1 <;>
    rcases max_choice (Tp 2 ρ s t) (Tp 3 ρ s t) with h2 | h2 <;>
    rcases max_choice (max (Tp 0 ρ s t) (Tp 1 ρ s t)) (max (Tp 2 ρ s t) (Tp 3 ρ s t)) with h | h <;>
    rw [h] <;> first
      | (rw [h1]; exact ⟨_, by norm_num, rfl⟩)
      | (rw [h2]; exact ⟨_, by norm_num, rfl⟩)

theorem rho_bounds {n : ℕ} (hn : 3 ≤ n) : -1 / 8 ≤ (-1 / 2 : ℝ) ^ n ∧ (-1 / 2 : ℝ) ^ n ≤ 1 / 16 := by
  rcases Nat.lt_or_ge n 4 with h | h
  · obtain rfl : n = 3 := by omega
    norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    have hm : |(-1 / 2 : ℝ) ^ m| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (by norm_num) (by norm_num [abs_div])
    rw [pow_add]
    have := abs_le.1 hm
    constructor <;> nlinarith
