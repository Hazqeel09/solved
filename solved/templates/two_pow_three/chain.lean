
theorem Q3_base {s t : ℝ} (hs0 : 0 ≤ s) (ht0 : 0 ≤ t) : Q3 0 s t = 2 * Fp 3 s t := by
  rw [Q3_zero]; simp only [P0, Fp]
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (3 - 1) * s + t)]
  rcases le_total s t with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ t - s), max_eq_left (by linarith)]; ring
  · rw [abs_of_nonpos (by linarith : t - s ≤ 0), max_eq_right (by linarith)]; ring

open Finset in
/-- The chain bound at `P = 3`. -/
theorem chain3_le {σ τ z w : ℕ → ℝ} {n : ℕ}
    (hz : ∀ k < n, z k = 0 ∨ z k = 1) (hw : ∀ k < n, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < n, σ k = (σ (k + 1) + z k) / 2) (hτ : ∀ k < n, τ k = (τ (k + 1) + w k) / 2)
    (hs0 : 0 ≤ σ n) (hs1 : σ n ≤ 1) (ht0 : 0 ≤ τ n) (ht1 : τ n ≤ 1) :
    2 * (Fp 3 (σ 0) (τ 0) + ∑ k ∈ range n, Fp 3 (σ k - σ (k + 1)) (τ k - τ (k + 1))) ≤
      Q3 n (σ n) (τ n) := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]; rw [Q3_base hs0 ht0]
  | succ n ih =>
    have hzn := hz n (by omega); have hwn := hw n (by omega)
    have en := hσ n (by omega); have fn := hτ n (by omega)
    obtain ⟨hs0', hs1'⟩ := state_bounds hzn en hs0 hs1
    obtain ⟨ht0', ht1'⟩ := state_bounds hwn fn ht0 ht1
    have ih' := ih (fun k hk => hz k (by omega)) (fun k hk => hw k (by omega))
      (fun k hk => hσ k (by omega)) (fun k hk => hτ k (by omega)) hs0' hs1' ht0' ht1'
    have hst := Q3_step n hs0 hs1 ht0 ht1 hzn hwn
    rw [Finset.sum_range_succ,
      show σ n - σ (n + 1) = (z n - σ (n + 1)) / 2 by rw [en]; ring,
      show τ n - τ (n + 1) = (w n - τ (n + 1)) / 2 by rw [fn]; ring]
    rw [en, fn] at ih'
    linarith

open Finset in
/-- Attainment at `P = 3`: every top state has bits whose chain sum reaches `Q3 n`. -/
theorem chain3_attain {n : ℕ} {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∃ σ τ z w : ℕ → ℝ, (∀ k < n, z k = 0 ∨ z k = 1) ∧ (∀ k < n, w k = 0 ∨ w k = 1) ∧
      (∀ k < n, σ k = (σ (k + 1) + z k) / 2) ∧ (∀ k < n, τ k = (τ (k + 1) + w k) / 2) ∧
      σ n = s ∧ τ n = t ∧
      Q3 n s t ≤ 2 * (Fp 3 (σ 0) (τ 0) + ∑ k ∈ range n, Fp 3 (σ k - σ (k + 1)) (τ k - τ (k + 1))) := by
  induction n generalizing s t with
  | zero =>
    refine ⟨fun _ => s, fun _ => t, fun _ => 0, fun _ => 0, fun k hk => absurd hk (by omega),
      fun k hk => absurd hk (by omega), fun k hk => absurd hk (by omega),
      fun k hk => absurd hk (by omega), rfl, rfl, ?_⟩
    simp only [Finset.range_zero, Finset.sum_empty, add_zero]; rw [Q3_base hs0 ht0]
  | succ n ih =>
    obtain ⟨z₀, w₀, hz₀, hw₀, hst⟩ := Q3_attain n hs0 hs1 ht0 ht1
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
      have hk : ∀ k ∈ range n, Fp 3 (Function.update σ (n + 1) s k -
            Function.update σ (n + 1) s (k + 1))
          (Function.update τ (n + 1) t k - Function.update τ (n + 1) t (k + 1)) =
          Fp 3 (σ k - σ (k + 1)) (τ k - τ (k + 1)) := by
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
      have : Fp 3 ((s + z₀) / 2 - s) ((t + w₀) / 2 - t) = Fp 3 ((z₀ - s) / 2) ((w₀ - t) / 2) := by
        congr 1 <;> ring
      rw [this]
      linarith

/-- The top state: `2^(a-1) Q3 a 1 0 = c_a · 3 - d_a`, and `z_a = 0` is no better. -/
theorem Q3_top {a : ℕ} (ha : 2 ≤ a) :
    Q3 a 0 0 ≤ Q3 a 1 0 ∧ 2 ^ (a - 1) * Q3 a 1 0 = Emax 3 a := by
  rcases Nat.lt_or_ge a 3 with h | h
  · obtain rfl : a = 2 := by omega
    rw [Q3_two, Q3_two]; unfold Q2 Emax; simp only [P2, Tp]; norm_num
  · obtain ⟨m, rfl⟩ : ∃ m, a = m + 3 := ⟨a - 3, by omega⟩
    obtain ⟨hρ0, hρ1⟩ := rho_bounds (n := m + 3) (by omega)
    rw [Q3_add3, Q3_add3]
    have h1 : U3 ((-1 / 2 : ℝ) ^ (m + 3)) 1 0 = 2 / 3 + 20 / 9 * (-1 / 2 : ℝ) ^ (m + 3) := by
      have e : Tp 1 ((-1 / 2 : ℝ) ^ (m + 3)) 1 0 = 2 / 3 + 20 / 9 * (-1 / 2 : ℝ) ^ (m + 3) := by
        simp only [Tp]; ring
      rw [← e]
      refine le_antisymm ?_ (Tp_le_U3 (by norm_num) _ _ _)
      unfold U3
      refine max_le (max_le ?_ le_rfl) (max_le ?_ ?_) <;> simp only [Tp] <;> nlinarith
    have h0 : U3 ((-1 / 2 : ℝ) ^ (m + 3)) 0 0 ≤ 2 / 3 + 20 / 9 * (-1 / 2 : ℝ) ^ (m + 3) := by
      unfold U3; simp only [Tp]
      refine max_le (max_le ?_ ?_) (max_le ?_ ?_) <;> nlinarith
    refine ⟨by linarith, ?_⟩
    rw [h1]; unfold Emax
    have hpow : (2 : ℝ) ^ (m + 3) * (-1 / 2 : ℝ) ^ (m + 3) = (-1) ^ (m + 3) := by
      rw [← mul_pow]; norm_num
    rw [show m + 3 - 1 = m + 2 by omega]
    have h2 : (2 : ℝ) ^ (m + 3) = 2 * 2 ^ (m + 2) := by rw [pow_succ]; ring
    push_cast
    rw [h2] at hpow ⊢
    linear_combination (10 / 9 : ℝ) * hpow
