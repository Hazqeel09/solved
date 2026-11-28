
theorem max4_piece (f : ℕ → ℝ) :
    ∃ j ≤ 3, max (max (f 0) (f 1)) (max (f 2) (f 3)) = f j := by
  rcases max_choice (f 0) (f 1) with h1 | h1 <;>
    rcases max_choice (f 2) (f 3) with h2 | h2 <;>
    rcases max_choice (max (f 0) (f 1)) (max (f 2) (f 3)) with h | h <;>
    rw [h] <;> first
      | (rw [h1]; exact ⟨_, by norm_num, rfl⟩)
      | (rw [h2]; exact ⟨_, by norm_num, rfl⟩)

theorem Q2_piece (s t : ℝ) : ∃ j ≤ 5, Q2 s t = P2 j s t := by
  unfold Q2
  obtain ⟨j, hj, h⟩ := max4_piece (fun i => P2 i s t)
  rcases max_choice (max (max (P2 0 s t) (P2 1 s t)) (max (P2 2 s t) (P2 3 s t)))
      (max (P2 4 s t) (P2 5 s t)) with h' | h'
  · rw [h', h]; exact ⟨j, by omega, rfl⟩
  · rw [h']
    rcases max_choice (P2 4 s t) (P2 5 s t) with h'' | h''
    · rw [h'']; exact ⟨4, by norm_num, rfl⟩
    · rw [h'']; exact ⟨5, by norm_num, rfl⟩

theorem le_max4 (f : ℕ → ℝ) {j : ℕ} (hj : j ≤ 3) : f j ≤ max (max (f 0) (f 1)) (max (f 2) (f 3)) := by
  interval_cases j
  · exact (le_max_left _ _).trans (le_max_left _ _)
  · exact (le_max_right _ _).trans (le_max_left _ _)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

theorem P2_le_Q2 {j : ℕ} (hj : j ≤ 5) (s t : ℝ) : P2 j s t ≤ Q2 s t := by
  unfold Q2
  rcases Nat.lt_or_ge j 4 with h | h
  · exact (le_max4 (fun i => P2 i s t) (by omega)).trans (le_max_left _ _)
  · obtain rfl | rfl : j = 4 ∨ j = 5 := by omega
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · exact (le_max_right _ _).trans (le_max_right _ _)

/-- Attainment of the step from `n` to `n + 1`: some bits make it an equality. -/
theorem Q3_attain (n : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ z w : ℝ, (z = 0 ∨ z = 1) ∧ (w = 0 ∨ w = 1) ∧
      Q3 (n + 1) s t ≤ 2 * Fp 3 ((z - s) / 2) ((w - t) / 2) + Q3 n ((s + z) / 2) ((t + w) / 2) := by
  match n with
  | 0 =>
    simp only [zero_add, Q3_zero, Q3_one, V1]
    obtain ⟨j, hj, h⟩ := max4_piece (fun i => P1 i s t)
    rw [h]
    interval_cases j
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, (at01_0 hs0 hs1 ht0 ht1).trans (by gcongr; exact le_max_right _ _)⟩
    · exact ⟨1, 1, Or.inr rfl, Or.inr rfl, (at01_1 hs0 hs1 ht0 ht1).trans (by gcongr; exact le_max_left _ _)⟩
    · exact ⟨1, 1, Or.inr rfl, Or.inr rfl, (at01_2 hs0 hs1 ht0 ht1).trans (by gcongr; exact le_max_right _ _)⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, (at01_3 hs0 hs1 ht0 ht1).trans (by gcongr; exact le_max_right _ _)⟩
  | 1 =>
    simp only [Nat.reduceAdd, Q3_one, Q3_two]
    obtain ⟨j, hj, h⟩ := Q2_piece s t
    rw [h]
    have L := fun {i : ℕ} (hi : i ≤ 3) (x y : ℝ) => le_max4 (fun k => P1 k x y) hi
    interval_cases j
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, (at12_0 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, (at12_1 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, (at12_2 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
    · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, (at12_3 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, (at12_4 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, (at12_5 hs0 hs1 ht0 ht1).trans (by gcongr; exact L (by norm_num) _ _)⟩
  | 2 =>
    simp only [Nat.reduceAdd, Q3_two, Q3_three, U3]
    obtain ⟨j, hj, h⟩ := max4_piece (fun i => Tp i (-1 / 8) s t)
    rw [h]
    interval_cases j
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, by
        have := at23_0 hs0 hs1 ht0 ht1; have := P2_le_Q2 (j := 1) (by norm_num) ((s + 1) / 2) ((t + 0) / 2)
        linarith⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, by
        have := at23_1 hs0 hs1 ht0 ht1; have := P2_le_Q2 (j := 0) (by norm_num) ((s + 0) / 2) ((t + 1) / 2)
        linarith⟩
    · exact ⟨0, 1, Or.inl rfl, Or.inr rfl, by
        have := at23_2 hs0 hs1 ht0 ht1; have := P2_le_Q2 (j := 0) (by norm_num) ((s + 0) / 2) ((t + 1) / 2)
        linarith⟩
    · exact ⟨1, 0, Or.inr rfl, Or.inl rfl, by
        have := at23_3 hs0 hs1 ht0 ht1; have := P2_le_Q2 (j := 1) (by norm_num) ((s + 1) / 2) ((t + 0) / 2)
        linarith⟩
  | m + 3 =>
    obtain ⟨hρ0, hρ1⟩ := rho_bounds (n := m + 3) (by omega)
    rw [show m + 3 + 1 = (m + 1) + 3 by omega]
    simp only [Q3_add3]
    rw [show (-1 / 2 : ℝ) ^ (m + 1 + 3) = -1 / 2 * (-1 / 2 : ℝ) ^ (m + 3) by ring]
    obtain ⟨j, hj, h⟩ := U3_piece (-1 / 2 * (-1 / 2 : ℝ) ^ (m + 3)) s t
    rw [h]
    have hc : (10 : ℝ) / 3 * ((m + 1 + 3 : ℕ) : ℝ) = 10 / 3 * ((m + 3 : ℕ) : ℝ) + 10 / 3 := by
      push_cast; ring
    rw [hc]
    interval_cases j
    · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
      have e := slkA_mid hρ0 hρ1 (atr_0_lo hs0 hs1 ht0 ht1) (atr_0_hi hs0 hs1 ht0 ht1)
      unfold slkA at e
      have := Tp_le_U3 (j := 1) (by norm_num) ((-1 / 2 : ℝ) ^ (m + 3)) ((s + 1) / 2) ((t + 0) / 2)
      linarith
    · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
      have e := slkA_mid hρ0 hρ1 (atr_1_lo hs0 hs1 ht0 ht1) (atr_1_hi hs0 hs1 ht0 ht1)
      unfold slkA at e
      have := Tp_le_U3 (j := 0) (by norm_num) ((-1 / 2 : ℝ) ^ (m + 3)) ((s + 0) / 2) ((t + 1) / 2)
      linarith
    · refine ⟨0, 1, Or.inl rfl, Or.inr rfl, ?_⟩
      have e := slkA_mid hρ0 hρ1 (atr_2_lo hs0 hs1 ht0 ht1) (atr_2_hi hs0 hs1 ht0 ht1)
      unfold slkA at e
      have := Tp_le_U3 (j := 0) (by norm_num) ((-1 / 2 : ℝ) ^ (m + 3)) ((s + 0) / 2) ((t + 1) / 2)
      linarith
    · refine ⟨1, 0, Or.inr rfl, Or.inl rfl, ?_⟩
      have e := slkA_mid hρ0 hρ1 (atr_3_lo hs0 hs1 ht0 ht1) (atr_3_hi hs0 hs1 ht0 ht1)
      unfold slkA at e
      have := Tp_le_U3 (j := 1) (by norm_num) ((-1 / 2 : ℝ) ^ (m + 3)) ((s + 1) / 2) ((t + 0) / 2)
      linarith
