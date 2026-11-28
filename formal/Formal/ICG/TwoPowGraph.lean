import Formal.ICG.TwoPowChain
import Research.ICGGeneralBridge

noncomputable section
namespace Solved.ICG.TwoPow

open Finset ICGGeneral

/-- `‖T_1(x) v‖₁ = F(v₀, v₁)` for `x ≥ 1`. -/
theorem L1_one {x : ℝ} (hx : 1 ≤ x) (v : ℕ → ℝ) : L1 x 1 v = Fp x (v 0) (v 1) := by
  have hx0 : 0 < x := by linarith
  rw [L1_path hx0, Finset.sum_range_one, Zp_rec hx0.ne' 1 v (by norm_num), Zp_self]
  have e1 : (v 1 + (x - 1) * v 0) / x - v 1 = (x - 1) * (v 0 - v 1) / x := by
    field_simp; ring
  rw [e1, abs_div, abs_div, abs_of_pos hx0, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - 1),
    abs_sub_comm (v 0), pow_one, mul_add, mul_div_cancel₀ _ hx0.ne', mul_div_cancel₀ _ hx0.ne']
  unfold Fp; ring_nf

/-- The indicator matrix of `S` on the exponent box of `2^a P`. -/
def Ys (P : ℕ) (S : Finset ℕ) (c e : ℕ) : ℝ := if 2 ^ c * P ^ e ∈ S then 1 else 0

theorem energy_eq_chain (P a : ℕ) (hP : P.Prime) (h2P : 2 ≠ P) (S : Finset ℕ) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) =
      2 ^ a * (Fp P (zeta 2 a (Ys P S) 0 0) (zeta 2 a (Ys P S) 0 1) +
        ∑ k ∈ range a, Fp P (zeta 2 a (Ys P S) k 0 - zeta 2 a (Ys P S) (k + 1) 0)
          (zeta 2 a (Ys P S) k 1 - zeta 2 a (Ys P S) (k + 1) 1)) := by
  have h := energy_icgAdj_pq 2 P a 1 Nat.prime_two hP h2P S
  rw [pow_one, Nat.cast_ofNat] at h
  rw [h, L1mat_path (by norm_num : (0 : ℝ) < 2)]
  simp only [L1_one (by exact_mod_cast hP.one_lt.le : (1 : ℝ) ≤ P)]
  rfl

theorem Ys_bit (P : ℕ) (S : Finset ℕ) (c e : ℕ) : Ys P S c e = 0 ∨ Ys P S c e = 1 := by
  unfold Ys; split_ifs <;> simp

theorem zeta_rec_two (P : ℕ) (S : Finset ℕ) {a : ℕ} (l : ℕ) {k : ℕ} (hk : k < a) :
    zeta 2 a (Ys P S) k l = (zeta 2 a (Ys P S) (k + 1) l + Ys P S k l) / 2 := by
  rw [zeta_rec (by norm_num) _ hk]; ring

theorem not_mem_top {P a : ℕ} {S : Finset ℕ} (hS : S ⊆ (2 ^ a * P).properDivisors) :
    Ys P S a 1 = 0 := by
  unfold Ys
  rw [ite_eq_right_iff]
  intro h
  have := hS h
  rw [pow_one, Nat.mem_properDivisors] at this
  exact absurd this.2 (lt_irrefl _)

/-- The closed form `c_a P - d_a`. -/
def Emax (P : ℝ) (a : ℕ) : ℝ :=
  (2 ^ a * (3 * a + 4) + 2 * (-1) ^ a) * P / 3 - (2 ^ a * (12 * a + 10) + 8 * (-1) ^ a) / 9

/-- **Upper bound for `n = 2^a P`.** -/
theorem energy_le {P a : ℕ} (hP : P.Prime) (hP5 : 5 ≤ P) (ha : 2 ≤ a) {S : Finset ℕ}
    (hS : S ⊆ (2 ^ a * P).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
      Emax P a := by
  have hP5' : (5 : ℝ) ≤ P := by exact_mod_cast hP5
  rw [energy_eq_chain P a hP (by omega) S]
  have htop := not_mem_top hS
  have hc := chain_le hP5' ha (σ := fun k => zeta 2 a (Ys P S) k 0)
    (τ := fun k => zeta 2 a (Ys P S) k 1) (z := fun k => Ys P S k 0) (w := fun k => Ys P S k 1)
    (fun k _ => Ys_bit P S k 0) (fun k _ => Ys_bit P S k 1) (fun k hk => zeta_rec_two P S 0 hk)
    (fun k hk => zeta_rec_two P S 1 hk)
    (by simp only [zeta_last]; rcases Ys_bit P S a 0 with h | h <;> simp [h])
    (by simp only [zeta_last]; rcases Ys_bit P S a 0 with h | h <;> simp [h])
    (by simp only [zeta_last, htop]; norm_num) (by simp only [zeta_last, htop]; norm_num)
  simp only [zeta_last, htop] at hc
  obtain ⟨ht1, ht2⟩ := Wb_top hP5' (by omega : 1 ≤ a) (Ys_bit P S a 0)
  unfold Emax
  calc _ ≤ 2 ^ a * Wb P a (Ys P S a 0) 0 := mul_le_mul_of_nonneg_left hc (by positivity)
    _ ≤ _ := ht1.trans ht2.le

theorem two_pow_ne_mul {P c d : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) : 2 ^ c ≠ 2 ^ d * P := by
  intro h
  have hdvd : P ∣ 2 ^ c := ⟨2 ^ d, by rw [h]; ring⟩
  exact hP2 ((Nat.prime_dvd_prime_iff_eq hP Nat.prime_two).1 (hP.dvd_of_dvd_pow hdvd))

/-- The set with prescribed bits: `2^a`, the `2^k` with `z_k = 1` and the `2^k P` with
`w_k = 1`, for `k < a`. -/
def setOf (P a : ℕ) (z w : ℕ → ℝ) : Finset ℕ :=
  insert (2 ^ a) ((((Finset.range a).filter fun k => z k = 1).image fun k => 2 ^ k) ∪
    ((Finset.range a).filter fun k => w k = 1).image fun k => 2 ^ k * P)

theorem setOf_sub {P a : ℕ} (hP : P.Prime) (z w : ℕ → ℝ) :
    setOf P a z w ⊆ (2 ^ a * P).properDivisors := by
  intro d hd
  have hP1 := hP.one_lt
  have hpos : 0 < 2 ^ a := by positivity
  simp only [setOf, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range] at hd
  rw [Nat.mem_properDivisors]
  rcases hd with rfl | ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
  · exact ⟨dvd_mul_right _ _, by nlinarith⟩
  · have : 2 ^ k ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) hk.le
    exact ⟨(pow_dvd_pow 2 hk.le).mul_right _, by nlinarith⟩
  · have : 2 ^ k < 2 ^ a := Nat.pow_lt_pow_right (by norm_num) hk
    exact ⟨mul_dvd_mul_right (pow_dvd_pow 2 hk.le) _, by nlinarith⟩

theorem mem_setOf0 {P a : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ} {c : ℕ} (hc : c ≤ a) :
    2 ^ c ∈ setOf P a z w ↔ c = a ∨ (c < a ∧ z c = 1) := by
  have inj : ∀ {i j : ℕ}, 2 ^ i = 2 ^ j → i = j := fun h => Nat.pow_right_injective (le_refl 2) h
  simp only [setOf, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨k, ⟨hk, hz⟩, h⟩ | ⟨k, -, h⟩)
    · exact Or.inl (inj h)
    · exact Or.inr (inj h ▸ ⟨hk, hz⟩)
    · exact absurd h.symm (two_pow_ne_mul hP hP2)
  · rintro (rfl | ⟨hlt, h⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨c, ⟨hlt, h⟩, rfl⟩)

theorem mem_setOf1 {P a : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ} {c : ℕ} :
    2 ^ c * P ∈ setOf P a z w ↔ c < a ∧ w c = 1 := by
  have inj : ∀ {i j : ℕ}, 2 ^ i = 2 ^ j → i = j := fun h => Nat.pow_right_injective (le_refl 2) h
  simp only [setOf, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_range]
  constructor
  · rintro (h | ⟨k, -, h⟩ | ⟨k, ⟨hk, hw⟩, h⟩)
    · exact absurd h.symm (two_pow_ne_mul hP hP2)
    · exact absurd h (two_pow_ne_mul hP hP2)
    · have := inj (Nat.eq_of_mul_eq_mul_right hP.pos h); exact this ▸ ⟨hk, hw⟩
  · rintro ⟨hlt, h⟩
    exact Or.inr (Or.inr ⟨c, ⟨hlt, h⟩, rfl⟩)

theorem Ys_setOf {P a : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ}
    (hz : ∀ k < a, z k = 0 ∨ z k = 1) (hw : ∀ k < a, w k = 0 ∨ w k = 1) {c : ℕ} (hc : c ≤ a) :
    Ys P (setOf P a z w) c 0 = (if c = a then 1 else z c) ∧
      Ys P (setOf P a z w) c 1 = (if c = a then 0 else w c) := by
  unfold Ys
  rw [pow_zero, mul_one, pow_one]
  constructor
  · by_cases hm : 2 ^ c ∈ setOf P a z w
    · rw [ite_eq_left hm]
      rcases (mem_setOf0 hP hP2 hc).1 hm with rfl | ⟨hlt, h⟩
      · rw [ite_eq_left rfl]
      · rw [ite_eq_right hlt.ne, h]
    · rw [ite_eq_right hm]
      have := mt (mem_setOf0 hP hP2 (z := z) (w := w) hc).2 hm
      push Not at this
      have hca : c ≠ a := this.1
      rw [ite_eq_right hca]
      rcases hz c (lt_of_le_of_ne hc hca) with h | h
      · exact h.symm
      · exact absurd h (this.2 (lt_of_le_of_ne hc hca))
  · by_cases hm : 2 ^ c * P ∈ setOf P a z w
    · rw [ite_eq_left hm]
      obtain ⟨hlt, h⟩ := (mem_setOf1 hP hP2).1 hm
      rw [ite_eq_right hlt.ne, h]
    · rw [ite_eq_right hm]
      by_cases hca : c = a
      · rw [ite_eq_left hca]
      · rw [ite_eq_right hca]
        have hlt := lt_of_le_of_ne hc hca
        rcases hw c hlt with h | h
        · exact h.symm
        · exact absurd ((mem_setOf1 hP hP2).2 ⟨hlt, h⟩) hm

/-- **The maximal energy of `ICG(2^a P, S)`.** For every prime `P ≥ 5` and every `a ≥ 2`,
`max_S E(ICG(2^a P, S)) = c_a P - d_a` with
`c_a = (2^a (3a + 4) + 2(-1)^a)/3` and `d_a = (2^a (12a + 10) + 8(-1)^a)/9`. -/
theorem energy_max {P a : ℕ} (hP : P.Prime) (hP5 : 5 ≤ P) (ha : 2 ≤ a) :
    (∀ S ⊆ (2 ^ a * P).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        Emax P a) ∧
    ∃ S ⊆ (2 ^ a * P).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) =
        Emax P a := by
  refine ⟨fun S hS => energy_le hP hP5 ha hS, ?_⟩
  have hP5' : (5 : ℝ) ≤ P := by exact_mod_cast hP5
  have hP2 : P ≠ 2 := by omega
  obtain ⟨σ, τ, z, w, hz, hw, hσ, hτ, hσa, hτa, hsum⟩ :=
    chain_attain hP5' ha (s := 1) (t := 0) (by norm_num) le_rfl le_rfl (by norm_num)
  set S := setOf P a z w
  refine ⟨S, setOf_sub hP z w, le_antisymm (energy_le hP hP5 ha (setOf_sub hP z w)) ?_⟩
  have hY := fun {c : ℕ} (hc : c ≤ a) => Ys_setOf hP hP2 hz hw hc
  -- the bridge path of `S` is the chain `σ, τ`
  have hpath : ∀ j ≤ a, zeta 2 a (Ys P S) (a - j) 0 = σ (a - j) ∧
      zeta 2 a (Ys P S) (a - j) 1 = τ (a - j) := by
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
      rw [zeta_rec_two P S 0 hk, zeta_rec_two P S 1 hk, hk1, ih0, ih1, hσ _ hk, hτ _ hk, hk1,
        (hY hk.le).1, (hY hk.le).2, ite_eq_right hne, ite_eq_right hne]
      exact ⟨rfl, rfl⟩
  have hp : ∀ k ≤ a, zeta 2 a (Ys P S) k 0 = σ k ∧ zeta 2 a (Ys P S) k 1 = τ k := by
    intro k hk
    have := hpath (a - k) (by omega)
    rwa [Nat.sub_sub_self hk] at this
  rw [energy_eq_chain P a hP (by omega) S]
  have hsum' : ∑ k ∈ Finset.range a, Fp P (zeta 2 a (Ys P S) k 0 - zeta 2 a (Ys P S) (k + 1) 0)
      (zeta 2 a (Ys P S) k 1 - zeta 2 a (Ys P S) (k + 1) 1) =
      ∑ k ∈ Finset.range a, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) := by
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Finset.mem_range.1 hk
    rw [(hp k hk'.le).1, (hp k hk'.le).2, (hp (k + 1) hk').1, (hp (k + 1) hk').2]
  rw [hsum', (hp 0 (by omega)).1, (hp 0 (by omega)).2]
  obtain ⟨-, ht2⟩ := Wb_top hP5' (by omega : 1 ≤ a) (Or.inr rfl : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1)
  unfold Emax
  rw [← ht2]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end Solved.ICG.TwoPow
