import Formal.ICG.TwoPb.Graph
import Formal.ICG.TwoPb.AttainSteps

/-!
# The maximal energy of `ICG(2 p^b, S)`

`energy_max`: for every odd prime `p` and every `b ≥ 2`,
`max_S E(ICG(2 p^b, S)) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`, `ε = (1, -1, -1, 1)` repeating.

The maximum is attained by `S* = {p^b} ∪ {p^k : z_k = 1} ∪ {2 p^k : w_k = 1}` (`k < b`), where the corner
`(z_k, w_k)` of step `k` walks the 4-cycle `(0,0) → (0,1) → (1,1) → (1,0)` from the top, forwards for
`b ≡ 0, 3 (mod 4)` and backwards otherwise (`cycZ`, `cycW`). Along its path every step is tight
(`lower_step`, `lower_base`), so the chain value is at least the path piece at the top, `K S(b)`.
-/

noncomputable section

open Finset ICGGeneral

namespace Solved.ICG.TwoPb

/-! ## The divisor set with prescribed bits -/

/-- `{P^b} ∪ {P^k : k < b, z_k = 1} ∪ {P^k 2 : k < b, w_k = 1}`. -/
def setP (P b : ℕ) (z w : ℕ → ℝ) : Finset ℕ :=
  insert (P ^ b) ((((range b).filter fun k => z k = 1).image fun k => P ^ k) ∪
    ((range b).filter fun k => w k = 1).image fun k => P ^ k * 2)

theorem pow_ne_pow_mul_two {P c d : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) : P ^ c ≠ P ^ d * 2 := by
  intro h
  have h2 : 2 ∣ P ^ c := ⟨P ^ d, by rw [h]; ring⟩
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hP).1 (Nat.prime_two.dvd_of_dvd_pow h2)
  exact hP2 this.symm

theorem setP_sub {P b : ℕ} (hP : P.Prime) (z w : ℕ → ℝ) :
    setP P b z w ⊆ (2 * P ^ b).properDivisors := by
  intro d hd
  have hP1 := hP.one_lt
  have hpos : 0 < P ^ b := by positivity
  simp only [setP, mem_insert, mem_union, mem_image, mem_filter, mem_range] at hd
  rw [Nat.mem_properDivisors]
  rcases hd with rfl | ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩
  · exact ⟨dvd_mul_left _ _, by omega⟩
  · have : P ^ k ≤ P ^ b := Nat.pow_le_pow_right hP.pos hk.le
    exact ⟨(pow_dvd_pow P hk.le).mul_left _, by omega⟩
  · have : P ^ k < P ^ b := Nat.pow_lt_pow_right hP1 hk
    refine ⟨?_, by omega⟩
    rw [mul_comm 2]
    exact mul_dvd_mul_right (pow_dvd_pow P hk.le) _

theorem pow_inj {P : ℕ} (hP : P.Prime) {i j : ℕ} (h : P ^ i = P ^ j) : i = j :=
  Nat.pow_right_injective hP.two_le h

theorem mem_setP0 {P b : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ} {c : ℕ} :
    P ^ c ∈ setP P b z w ↔ c = b ∨ (c < b ∧ z c = 1) := by
  simp only [setP, mem_insert, mem_union, mem_image, mem_filter, mem_range]
  constructor
  · rintro (h | ⟨k, ⟨hk, hz⟩, h⟩ | ⟨k, -, h⟩)
    · exact Or.inl (pow_inj hP h)
    · exact Or.inr (pow_inj hP h ▸ ⟨hk, hz⟩)
    · exact absurd h.symm (pow_ne_pow_mul_two hP hP2)
  · rintro (rfl | ⟨hlt, h⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨c, ⟨hlt, h⟩, rfl⟩)

theorem mem_setP1 {P b : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ} {c : ℕ} :
    P ^ c * 2 ∈ setP P b z w ↔ c < b ∧ w c = 1 := by
  simp only [setP, mem_insert, mem_union, mem_image, mem_filter, mem_range]
  constructor
  · rintro (h | ⟨k, -, h⟩ | ⟨k, ⟨hk, hw⟩, h⟩)
    · exact absurd h.symm (pow_ne_pow_mul_two hP hP2)
    · exact absurd h (pow_ne_pow_mul_two hP hP2)
    · have := pow_inj hP (Nat.eq_of_mul_eq_mul_right (by norm_num) h); exact this ▸ ⟨hk, hw⟩
  · rintro ⟨hlt, h⟩
    exact Or.inr (Or.inr ⟨c, ⟨hlt, h⟩, rfl⟩)

theorem Yp_setP {P b : ℕ} (hP : P.Prime) (hP2 : P ≠ 2) {z w : ℕ → ℝ}
    (hz : ∀ k < b, z k = 0 ∨ z k = 1) (hw : ∀ k < b, w k = 0 ∨ w k = 1) {c : ℕ} (hc : c ≤ b) :
    Yp P (setP P b z w) c 0 = (if c = b then 1 else z c) ∧
      Yp P (setP P b z w) c 1 = (if c = b then 0 else w c) := by
  unfold Yp
  rw [pow_zero, mul_one, pow_one]
  constructor
  · by_cases hm : P ^ c ∈ setP P b z w
    · rw [ite_eq_left hm]
      rcases (mem_setP0 hP hP2).1 hm with rfl | ⟨hlt, h⟩
      · rw [ite_eq_left rfl]
      · rw [ite_eq_right hlt.ne, h]
    · rw [ite_eq_right hm]
      have := mt (mem_setP0 hP hP2 (z := z) (w := w)).2 hm
      push Not at this
      rw [ite_eq_right this.1]
      rcases hz c (lt_of_le_of_ne hc this.1) with h | h
      · exact h.symm
      · exact absurd h (this.2 (lt_of_le_of_ne hc this.1))
  · by_cases hm : P ^ c * 2 ∈ setP P b z w
    · rw [ite_eq_left hm]
      obtain ⟨hlt, h⟩ := (mem_setP1 hP hP2).1 hm
      rw [ite_eq_right hlt.ne, h]
    · rw [ite_eq_right hm]
      by_cases hcb : c = b
      · rw [ite_eq_left hcb]
      · rw [ite_eq_right hcb]
        have hlt := lt_of_le_of_ne hc hcb
        rcases hw c hlt with h | h
        · exact h.symm
        · exact absurd ((mem_setP1 hP hP2).2 ⟨hlt, h⟩) hm

/-! ## The maximiser and its value -/

theorem cycZ_bit (bm r : ℕ) : cycZ bm r = 0 ∨ cycZ bm r = 1 := by
  unfold cycZ; split_ifs <;> simp

theorem cycW_bit (bm r : ℕ) : cycW bm r = 0 ∨ cycW bm r = 1 := by
  unfold cycW; split_ifs <;> simp

/-- The bits of the maximiser at step `k` (from the bottom). -/
def zOpt (b k : ℕ) : ℝ := cycZ (b % 4) (b - 1 - k)

/-- The bits of the maximiser at step `k` (from the bottom). -/
def wOpt (b k : ℕ) : ℝ := cycW (b % 4) (b - 1 - k)

theorem KF2_term {y s' t' : ℝ} (hy : 0 ≤ y) (hs : 0 ≤ s') (ht : 0 ≤ t') :
    Kc y * F2 s' t' = max (2 * Kc y * s') (2 * Kc y * t') := by
  have hK : (0 : ℝ) ≤ 2 * Kc y := mul_nonneg zero_le_two (Kc_pos hy).le
  rw [F2_eq, abs_of_nonneg hs, abs_of_nonneg ht, ← mul_max_of_nonneg _ _ hK]
  ring

/-- The path piece at the top state `(1, 0)` is `K S(b)`. -/
theorem top_value {y : ℝ} (hy : 0 ≤ y) {b : ℕ} (hb : 2 ≤ b) :
    (b : ℝ) * Kg y + QL (b % 4) (b % 4) y (tauN y b) 1 0 = Kc y * Ssum (1 / (y + 3)) b := by
  unfold tauN mk
  rw [Ssum_closed, Kg_eq hy, betaS_mod]
  rcases mod4_cases b with h | h | h | h
  · rw [ite_eq_left h, h]
    have q : QL 0 0 y ((1 / (y + 3)) ^ (b - 4)) 1 0 = KS_0 y ((1 / (y + 3)) ^ (b - 4)) := by
      simp only [QL]; norm_num; exact start_eq_0 _ _
    rw [q, KS_0_eq hy, mul_assoc (betaS _ 0), ← pow_add, show 4 + (b - 4) = b by omega]
    ring
  · rw [ite_eq_right (by omega), h]
    have q : QL 1 1 y ((1 / (y + 3)) ^ (b - 1)) 1 0 = KS_1 y ((1 / (y + 3)) ^ (b - 1)) := by
      simp only [QL]; norm_num; exact start_eq_1 _ _
    rw [q, KS_1_eq hy, mul_assoc (betaS _ 1), ← pow_add, show 1 + (b - 1) = b by omega]
    ring
  · rw [ite_eq_right (by omega), h]
    have q : QL 2 2 y ((1 / (y + 3)) ^ (b - 2)) 1 0 = KS_2 y ((1 / (y + 3)) ^ (b - 2)) := by
      simp only [QL]; norm_num; exact start_eq_2 _ _
    rw [q, KS_2_eq hy, mul_assoc (betaS _ 2), ← pow_add, show 2 + (b - 2) = b by omega]
    ring
  · rw [ite_eq_right (by omega), h]
    have q : QL 3 3 y ((1 / (y + 3)) ^ (b - 3)) 1 0 = KS_3 y ((1 / (y + 3)) ^ (b - 3)) := by
      simp only [QL]; norm_num; exact start_eq_3 _ _
    rw [q, KS_3_eq hy, mul_assoc (betaS _ 3), ← pow_add, show 3 + (b - 3) = b by omega]
    ring

/-- **The lower chain bound** along the maximiser's path. -/
theorem lower_chain {y : ℝ} (hy : 0 ≤ y) {b : ℕ} (hb : 1 ≤ b) {σ τ : ℕ → ℝ}
    (hσ : ∀ k < b, (y + 3) * σ k = σ (k + 1) + (y + 2) * zOpt b k)
    (hτ : ∀ k < b, (y + 3) * τ k = τ (k + 1) + (y + 2) * wOpt b k)
    (hσb : 0 ≤ σ b ∧ σ b ≤ 1) (hτb : 0 ≤ τ b ∧ τ b ≤ 1) :
    (b : ℝ) * Kg y + QL (b % 4) (b % 4) y (tauN y b) (σ b) (τ b) ≤
      Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range b, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) := by
  have hz : ∀ k < b, zOpt b k = 0 ∨ zOpt b k = 1 := fun k _ => cycZ_bit _ _
  have hw : ∀ k < b, wOpt b k = 0 ∨ wOpt b k = 1 := fun k _ => cycW_bit _ _
  have box : ∀ j ≤ b, (0 ≤ σ (b - j) ∧ σ (b - j) ≤ 1) ∧ (0 ≤ τ (b - j) ∧ τ (b - j) ≤ 1) := by
    intro j hj
    induction j with
    | zero => simpa using ⟨hσb, hτb⟩
    | succ j ih =>
      obtain ⟨⟨a0, a1⟩, ⟨c0, c1⟩⟩ := ih (by omega)
      have hk : b - (j + 1) < b := by omega
      have e : b - (j + 1) + 1 = b - j := by omega
      have h1 := hσ _ hk; have h2 := hτ _ hk
      rw [e] at h1 h2
      exact ⟨step_box hy a0 a1 (hz _ hk) h1, step_box hy c0 c1 (hw _ hk) h2⟩
  have boxk : ∀ k ≤ b, (0 ≤ σ k ∧ σ k ≤ 1) ∧ (0 ≤ τ k ∧ τ k ≤ 1) := by
    intro k hk
    have := box (b - k) (by omega)
    rwa [Nat.sub_sub_self hk] at this
  have main : ∀ n, 1 ≤ n → n ≤ b →
      (n : ℝ) * Kg y + QL (b % 4) (n % 4) y (tauN y n) (σ n) (τ n) ≤
        Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range n, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) := by
    intro n hn hnb
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · obtain ⟨⟨a0, a1⟩, ⟨c0, c1⟩⟩ := boxk 1 hnb
        obtain ⟨⟨d0, -⟩, ⟨e0, -⟩⟩ := boxk 0 (by omega)
        have h1 := hσ 0 (by omega)
        have h2 := hτ 0 (by omega)
        unfold zOpt at h1; unfold wOpt at h2
        rw [Nat.sub_zero] at h1 h2
        have hl := lower_base hy hb a0 a1 c0 c1 h1 h2
        rw [← KF2 hy h1 h2, ← KF2_term hy d0 e0] at hl
        have hτ1 : tauN y (0 + 1) = 1 := by simp [tauN, mk]
        rw [hτ1]
        simp only [range_one, sum_singleton, zero_add, Nat.cast_one, one_mul,
          show (1 : ℕ) % 4 = 1 by norm_num]
        linarith
      · have ih' := ih hpos (by omega)
        obtain ⟨⟨a0, a1⟩, ⟨c0, c1⟩⟩ := boxk (n + 1) hnb
        have h1 := hσ n (by omega)
        have h2 := hτ n (by omega)
        unfold zOpt at h1; unfold wOpt at h2
        rw [show b - 1 - n = b - (n + 1) by omega] at h1 h2
        have hl := lower_step hy hpos hnb a0 a1 c0 c1 h1 h2
        rw [← KF2 hy h1 h2] at hl
        have e : Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range (n + 1), F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) =
            Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range n, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) +
              Kc y * F2 (σ n - σ (n + 1)) (τ n - τ (n + 1)) := by
          rw [sum_range_succ]; ring
        rw [e]
        push_cast
        linarith
  exact main b hb le_rfl

/-- **The maximal energy of `ICG(2 p^b, S)`.** For every odd prime `p` and every `b ≥ 2`,
`max_S E(ICG(2 p^b, S)) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)` with `ε = (1, -1, -1, 1)` repeating,
and the maximum is attained by `setP p b (zOpt b) (wOpt b)`. -/
theorem energy_max {p b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 2 ≤ b) :
    (∀ S ⊆ (2 * p ^ b).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * (p : ℝ) ^ (b - j)) ∧
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ b) (setP p b (zOpt b) (wOpt b)))
        (ICGBridge.icgAdj_isHermitian _ _) =
      2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * (p : ℝ) ^ (b - j) := by
  refine ⟨fun S hS => energy_le hp hp2 hb hS, ?_⟩
  set S := setP p b (zOpt b) (wOpt b)
  refine le_antisymm (energy_le hp hp2 hb (setP_sub hp _ _)) ?_
  have hp3 := three_le hp hp2
  set y : ℝ := (p : ℝ) - 3 with hydef
  have hy : 0 ≤ y := by linarith
  have hyp : y + 3 = p := by ring
  have hz : ∀ k < b, zOpt b k = 0 ∨ zOpt b k = 1 := fun k _ => cycZ_bit _ _
  have hw : ∀ k < b, wOpt b k = 0 ∨ wOpt b k = 1 := fun k _ => cycW_bit _ _
  have hY := fun {c : ℕ} (hc : c ≤ b) => Yp_setP hp hp2 hz hw hc
  have hrec : ∀ l, ∀ k < b, (y + 3) * zeta p b (Yp p S) k l =
      zeta p b (Yp p S) (k + 1) l + (y + 2) * Yp p S k l := by
    intro l k hk
    rw [zeta_rec_p p hp S l hk, hyp]
    field_simp
    ring
  have ht0 : zeta p b (Yp p S) b 0 = 1 := by rw [zeta_last, (hY le_rfl).1, ite_eq_left rfl]
  have ht1 : zeta p b (Yp p S) b 1 = 0 := by rw [zeta_last, (hY le_rfl).2, ite_eq_left rfl]
  have hlo := lower_chain hy (by omega : 1 ≤ b) (σ := fun k => zeta p b (Yp p S) k 0)
    (τ := fun k => zeta p b (Yp p S) k 1)
    (fun k hk => by rw [hrec 0 k hk, (hY hk.le).1, ite_eq_right hk.ne])
    (fun k hk => by rw [hrec 1 k hk, (hY hk.le).2, ite_eq_right hk.ne])
    (by simp only [ht0]; norm_num) (by simp only [ht1]; norm_num)
  simp only [ht0, ht1] at hlo
  rw [top_value hy hb, hyp] at hlo
  have hK := Kc_pos hy
  rw [energy_eq_chain p b hp hp2 S, ← Ssum_eq_poly (by positivity : (p : ℝ) ≠ 0)]
  exact mul_le_mul_of_nonneg_left (le_of_mul_le_mul_left hlo hK) (by positivity)

end Solved.ICG.TwoPb
