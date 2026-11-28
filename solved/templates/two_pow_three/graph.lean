
/-! ## Graph energy at `P = 3` -/

/-- **Upper bound for `n = 2^a · 3`.** -/
theorem energy_le_three {a : ℕ} (ha : 2 ≤ a) {S : Finset ℕ} (hS : S ⊆ (2 ^ a * 3).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * 3) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
      Emax 3 a := by
  have hP : Nat.Prime 3 := by norm_num
  have h := energy_eq_chain 3 a hP (by norm_num) S
  push_cast at h
  rw [h]
  have htop := not_mem_top hS
  have hc := chain3_le (σ := fun k => zeta 2 a (Ys 3 S) k 0) (τ := fun k => zeta 2 a (Ys 3 S) k 1)
    (z := fun k => Ys 3 S k 0) (w := fun k => Ys 3 S k 1) (n := a)
    (fun k _ => Ys_bit 3 S k 0) (fun k _ => Ys_bit 3 S k 1) (fun k hk => zeta_rec_two 3 S 0 hk)
    (fun k hk => zeta_rec_two 3 S 1 hk)
    (by simp only [zeta_last]; rcases Ys_bit 3 S a 0 with h | h <;> simp [h])
    (by simp only [zeta_last]; rcases Ys_bit 3 S a 0 with h | h <;> simp [h])
    (by simp only [zeta_last, htop]; norm_num) (by simp only [zeta_last, htop]; norm_num)
  simp only [zeta_last, htop] at hc
  obtain ⟨h01, htop'⟩ := Q3_top ha
  have hz : Q3 a (Ys 3 S a 0) 0 ≤ Q3 a 1 0 := by
    rcases Ys_bit 3 S a 0 with h0 | h0
    · rw [h0]; exact h01
    · rw [h0]
  have h2 : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [← htop', h2]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (a - 1)]

/-- **The maximal energy of `ICG(2^a · 3, S)`.** For every `a ≥ 2`,
`max_S E(ICG(2^a · 3, S)) = 3 c_a - d_a`. -/
theorem energy_max_three {a : ℕ} (ha : 2 ≤ a) :
    (∀ S ⊆ (2 ^ a * 3).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * 3) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        Emax 3 a) ∧
    ∃ S ⊆ (2 ^ a * 3).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * 3) S) (ICGBridge.icgAdj_isHermitian _ _) =
        Emax 3 a := by
  refine ⟨fun S hS => energy_le_three ha hS, ?_⟩
  have hP : Nat.Prime 3 := by norm_num
  obtain ⟨σ, τ, z, w, hz, hw, hσ, hτ, hσa, hτa, hsum⟩ :=
    chain3_attain (n := a) (s := 1) (t := 0) (by norm_num) le_rfl le_rfl (by norm_num)
  set S := setOf 3 a z w
  refine ⟨S, setOf_sub hP z w, le_antisymm (energy_le_three ha (setOf_sub hP z w)) ?_⟩
  have hY := fun {c : ℕ} (hc : c ≤ a) => Ys_setOf hP (by norm_num) hz hw hc
  have hpath : ∀ j ≤ a, zeta 2 a (Ys 3 S) (a - j) 0 = σ (a - j) ∧
      zeta 2 a (Ys 3 S) (a - j) 1 = τ (a - j) := by
    intro j hj
    induction j with
    | zero =>
      rw [Nat.sub_zero, zeta_last, zeta_last, (hY le_rfl).1, (hY le_rfl).2, ite_eq_left rfl,
        ite_eq_left rfl, hσa, hτa]
      exact ⟨rfl, rfl⟩
    | succ j ih =>
      obtain ⟨ih0, ih1⟩ := ih (by omega)
      have hk : a - (j + 1) < a := by omega
      have hk1 : a - (j + 1) + 1 = a - j := by omega
      have hne : a - (j + 1) ≠ a := by omega
      rw [zeta_rec_two 3 S 0 hk, zeta_rec_two 3 S 1 hk, hk1, ih0, ih1, hσ _ hk, hτ _ hk, hk1,
        (hY hk.le).1, (hY hk.le).2, ite_eq_right hne, ite_eq_right hne]
      exact ⟨rfl, rfl⟩
  have hp : ∀ k ≤ a, zeta 2 a (Ys 3 S) k 0 = σ k ∧ zeta 2 a (Ys 3 S) k 1 = τ k := by
    intro k hk
    have := hpath (a - k) (by omega)
    rwa [Nat.sub_sub_self hk] at this
  have h := energy_eq_chain 3 a hP (by norm_num) S
  push_cast at h
  rw [h]
  have hsum' : ∑ k ∈ Finset.range a, Fp 3 (zeta 2 a (Ys 3 S) k 0 - zeta 2 a (Ys 3 S) (k + 1) 0)
      (zeta 2 a (Ys 3 S) k 1 - zeta 2 a (Ys 3 S) (k + 1) 1) =
      ∑ k ∈ Finset.range a, Fp 3 (σ k - σ (k + 1)) (τ k - τ (k + 1)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [(hp k hk'.le).1, (hp k hk'.le).2, (hp (k + 1) hk').1, (hp (k + 1) hk').2]
  rw [hsum', (hp 0 (by omega)).1, (hp 0 (by omega)).2]
  obtain ⟨-, htop'⟩ := Q3_top ha
  have h2 : (2 : ℝ) ^ a = 2 * 2 ^ (a - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [← htop', h2]
  nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) (a - 1)]

/-- **The maximal energy of `ICG(2^a P, S)` for every odd prime `P` and `a ≥ 2`.** -/
theorem energy_max_odd {P a : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) (ha : 2 ≤ a) :
    (∀ S ⊆ (2 ^ a * P).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        Emax P a) ∧
    ∃ S ⊆ (2 ^ a * P).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) =
        Emax P a := by
  rcases Nat.lt_or_ge P 5 with h | h
  · have h3 : P = 3 := by
      have := hP.two_le
      interval_cases P <;> first | rfl | exact absurd rfl hP2 | exact absurd hP (by norm_num)
    subst h3
    simpa using energy_max_three ha
  · exact energy_max hP h ha
