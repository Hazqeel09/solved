import Formal.ICG.TwoPowTight
import Formal.ICG.TwoPowGraph

/-!
# The maximisers of `ICG(2^a P, S)`

`energy_eq_max_iff`: for a prime `P ≥ 5`, `a ≥ 2` and a set `S` of proper divisors of `2^a P`,
`E(ICG(2^a P, S))` is maximal exactly when `2^a, 2^(a-1) P, 1 ∈ S`, `2^(a-1), P ∉ S`, and for
`1 ≤ k ≤ a - 2` exactly one of `2^k, 2^k P` lies in `S`, alternating between consecutive `k`.
So there are two maximisers for `a ≥ 3` and one for `a = 2`.

Equality in the chain bound forces tight choices (`chain_eq_iff`). Tight choices take exactly one
of the two bits, so the chain stays on the anti-diagonal `σ + τ = 1`, where `Left` means
`σ ≤ 1/2`. Starting from `(1, 0)` the chain reaches `σ = 1/2` once, at level `a - 1`, and then
alternates strictly between the two sides (`path_facts`, `path_iff`).
-/

noncomputable section

namespace Solved.ICG.TwoPow

open Finset ICGGeneral

theorem down_ind {a : ℕ} {Q : ℕ → Prop} (htop : Q a) (hstep : ∀ j < a, Q (j + 1) → Q j) :
    ∀ j ≤ a, Q j := by
  have key : ∀ d, d ≤ a → Q (a - d) := by
    intro d
    induction d with
    | zero => intro _; simpa using htop
    | succ d ih =>
      intro hd
      have h := hstep (a - (d + 1)) (by omega)
      rw [show a - (d + 1) + 1 = a - d by omega] at h
      exact h (ih (by omega))
  intro j hj
  have := key (a - j) (by omega)
  rwa [Nat.sub_sub_self hj] at this

theorem left_anti {P s : ℝ} (hP : 5 ≤ P) : Left P s (1 - s) ↔ s ≤ 1 / 2 := by
  have h : 0 < Aq P + Bq P := by unfold Aq Bq; linarith
  unfold Left
  constructor
  · intro hl; by_contra hc; push Not at hc; nlinarith [mul_pos h (sub_pos.2 hc)]
  · intro hs; nlinarith [mul_nonneg h.le (sub_nonneg.2 hs)]

theorem right_anti {P s : ℝ} (hP : 5 ≤ P) : Right P s (1 - s) ↔ 1 / 2 ≤ s := by
  have h : 0 < Aq P + Bq P := by unfold Aq Bq; linarith
  unfold Right
  constructor
  · intro hl; by_contra hc; push Not at hc; nlinarith [mul_pos h (sub_pos.2 hc)]
  · intro hs; nlinarith [mul_nonneg h.le (sub_nonneg.2 hs)]

/-- Facts about a chain from the top state `(1, 0)` whose choices below the top each take exactly
one bit, with `(z, w) = (0, 1)` at level `a - 1`. -/
theorem path_facts {a : ℕ} (ha : 2 ≤ a) {σ τ z w : ℕ → ℝ} (hz : ∀ k < a, z k = 0 ∨ z k = 1)
    (hw : ∀ k < a, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < a, σ k = (σ (k + 1) + z k) / 2) (hτ : ∀ k < a, τ k = (τ (k + 1) + w k) / 2)
    (hσa : σ a = 1) (hτa : τ a = 0) (hone : ∀ k, 1 ≤ k → k < a → z k + w k = 1)
    (hza : z (a - 1) = 0) (hwa : w (a - 1) = 1) :
    (∀ j, 1 ≤ j → j ≤ a → τ j = 1 - σ j) ∧ σ (a - 1) = 1 / 2 ∧
      ∀ j, 1 ≤ j → j ≤ a - 2 → (z j = 1 → 1 / 2 < σ j) ∧ (z j = 0 → σ j < 1 / 2) := by
  have hanti : ∀ j ≤ a, 1 ≤ j → σ j + τ j = 1 := by
    refine down_ind (Q := fun j => 1 ≤ j → σ j + τ j = 1) (fun _ => by rw [hσa, hτa]; norm_num) ?_
    intro j hj ih h1
    rw [hσ j hj, hτ j hj]
    have := ih (by omega); have := hone j h1 hj
    linarith
  have hσpos : ∀ j ≤ a, 0 < σ j := by
    refine down_ind (Q := fun j => 0 < σ j) (by rw [hσa]; norm_num) ?_
    intro j hj ih
    rw [hσ j hj]; rcases hz j hj with h | h <;> rw [h] <;> linarith
  have hτpos : ∀ j ≤ a - 1, 0 < τ j := by
    refine down_ind (Q := fun j => 0 < τ j) ?_ ?_
    · rw [hτ (a - 1) (by omega), show a - 1 + 1 = a by omega, hτa, hwa]; norm_num
    · intro j hj ih
      rw [hτ j (by omega)]; rcases hw j (by omega) with h | h <;> rw [h] <;> linarith
  refine ⟨fun j h1 h2 => by linarith [hanti j h2 h1], ?_, fun j h1 h2 => ?_⟩
  · rw [hσ (a - 1) (by omega), show a - 1 + 1 = a by omega, hσa, hza]; norm_num
  · have hp := hσpos (j + 1) (by omega)
    have hq := hτpos (j + 1) (by omega)
    have ha' := hanti (j + 1) (by omega) (by omega)
    rw [hσ j (by omega)]
    constructor
    · intro h; rw [h]; linarith
    · intro h; rw [h]; linarith

/-- On a chain from `(1, 0)`, the choices below the top are all tight exactly when they follow
the local rule: `(0, 1)` at level `a - 1`, one bit at each level `1 ≤ k ≤ a - 2`, alternating. -/
theorem path_iff {P : ℝ} (hP : 5 ≤ P) {a : ℕ} (ha : 2 ≤ a) {σ τ z w : ℕ → ℝ}
    (hz : ∀ k < a, z k = 0 ∨ z k = 1) (hw : ∀ k < a, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < a, σ k = (σ (k + 1) + z k) / 2) (hτ : ∀ k < a, τ k = (τ (k + 1) + w k) / 2)
    (hσa : σ a = 1) (hτa : τ a = 0) :
    (∀ k, 1 ≤ k → k < a → Tight P (σ (k + 1)) (τ (k + 1)) (z k) (w k)) ↔
      z (a - 1) = 0 ∧ w (a - 1) = 1 ∧ (∀ k, 1 ≤ k → k ≤ a - 2 → z k + w k = 1) ∧
        ∀ k, 1 ≤ k → k + 1 ≤ a - 2 → z k + z (k + 1) = 1 := by
  have hA : 0 < Aq P := by unfold Aq; linarith
  have hB : 0 < Bq P := by unfold Bq; linarith
  have hnotL : ¬ Left P 1 0 := by unfold Left; intro h; linarith
  constructor
  · intro hT
    have hone : ∀ k, 1 ≤ k → k < a → z k + w k = 1 := fun k h1 h2 => by
      rcases hT k h1 h2 with ⟨h, h', -⟩ | ⟨h, h', -⟩ <;> rw [h, h'] <;> norm_num
    have htop := hT (a - 1) (by omega) (by omega)
    rw [show a - 1 + 1 = a by omega, hσa, hτa] at htop
    obtain ⟨hza, hwa⟩ : z (a - 1) = 0 ∧ w (a - 1) = 1 := by
      rcases htop with ⟨-, -, h⟩ | ⟨h, h', -⟩
      · exact absurd h hnotL
      · exact ⟨h, h'⟩
    obtain ⟨hanti, -, hside⟩ := path_facts ha hz hw hσ hτ hσa hτa hone hza hwa
    refine ⟨hza, hwa, fun k h1 h2 => hone k h1 (by omega), fun k h1 h2 => ?_⟩
    have hTk := hT k h1 (by omega)
    rw [hanti (k + 1) (by omega) (by omega)] at hTk
    obtain ⟨hs1, hs0⟩ := hside (k + 1) (by omega) h2
    rcases hTk with ⟨h, -, hL⟩ | ⟨h, -, hR⟩
    · rw [left_anti hP] at hL
      rcases hz (k + 1) (by omega) with h' | h'
      · rw [h, h']; norm_num
      · exact absurd (hs1 h') (not_lt.2 hL)
    · rw [right_anti hP] at hR
      rcases hz (k + 1) (by omega) with h' | h'
      · exact absurd (hs0 h') (not_lt.2 hR)
      · rw [h, h']; norm_num
  · rintro ⟨hza, hwa, hone', halt⟩
    have hone : ∀ k, 1 ≤ k → k < a → z k + w k = 1 := fun k h1 h2 => by
      rcases Nat.lt_or_ge k (a - 1) with h | h
      · exact hone' k h1 (by omega)
      · rw [show k = a - 1 by omega, hza, hwa]; norm_num
    obtain ⟨hanti, hmid, hside⟩ := path_facts ha hz hw hσ hτ hσa hτa hone hza hwa
    intro k h1 h2
    rcases Nat.lt_or_ge k (a - 1) with hk | hk
    · rw [hanti (k + 1) (by omega) (by omega)]
      have hzw := hone k h1 h2
      rcases hz k h2 with h | h
      · -- `w k = 1`: need `σ (k + 1) ≥ 1/2`
        refine Or.inr ⟨h, by linarith, (right_anti hP).2 ?_⟩
        rcases Nat.lt_or_ge (k + 1) (a - 1) with hk' | hk'
        · have := halt k h1 (by omega)
          rcases hz (k + 1) (by omega) with h' | h'
          · rw [h, h'] at this; norm_num at this
          · exact ((hside (k + 1) (by omega) (by omega)).1 h').le
        · rw [show k + 1 = a - 1 by omega, hmid]
      · refine Or.inl ⟨h, by linarith, (left_anti hP).2 ?_⟩
        rcases Nat.lt_or_ge (k + 1) (a - 1) with hk' | hk'
        · have := halt k h1 (by omega)
          rcases hz (k + 1) (by omega) with h' | h'
          · exact ((hside (k + 1) (by omega) (by omega)).2 h').le
          · rw [h, h'] at this; norm_num at this
        · rw [show k + 1 = a - 1 by omega, hmid]
    · have hka : k = a - 1 := by omega
      subst hka
      rw [show a - 1 + 1 = a by omega, hσa, hτa]
      refine Or.inr ⟨hza, hwa, ?_⟩
      unfold Right; linarith

theorem Wb_zero_lt {P : ℝ} (hP : 5 ≤ P) {a : ℕ} (ha : 2 ≤ a) : Wb P a 0 0 < Wb P a 1 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, a = m + 2 := ⟨a - 2, by omega⟩
  obtain ⟨hμ0, hμ1⟩ := neg_half_pow_bounds m
  have hc : 0 < 1 - (-1 / 2 : ℝ) ^ (m + 1) := by rw [pow_succ]; nlinarith
  have hΦ0 : Phi P 0 0 = 0 := by unfold Phi Aq Bq; rw [max_eq_left (by linarith)]; ring
  have hΦ1 : Phi P 1 0 = Bq P := by unfold Phi Aq Bq; rw [max_eq_right (by linarith)]; ring
  have hB : 0 < Bq P := by unfold Bq; linarith
  unfold Wb
  rw [hΦ0, hΦ1, show m + 2 - 1 = m + 1 by omega]
  nlinarith [mul_pos hc hB]

theorem Ys_zero_iff (P : ℕ) (S : Finset ℕ) (c : ℕ) : Ys P S c 0 = 1 ↔ 2 ^ c ∈ S := by
  unfold Ys; rw [pow_zero, mul_one]; split_ifs with h <;> simp [h]

theorem Ys_one_iff (P : ℕ) (S : Finset ℕ) (c : ℕ) : Ys P S c 1 = 1 ↔ 2 ^ c * P ∈ S := by
  unfold Ys; rw [pow_one]; split_ifs with h <;> simp [h]

theorem bits_sum_one {x y : ℝ} (hx : x = 0 ∨ x = 1) (hy : y = 0 ∨ y = 1) :
    x + y = 1 ↔ (x = 1 ↔ ¬ y = 1) := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> norm_num

theorem bit_zero_iff {x : ℝ} (hx : x = 0 ∨ x = 1) : x = 0 ↔ ¬ x = 1 := by
  rcases hx with rfl | rfl <;> norm_num

/-- **The maximisers of `ICG(2^a P, S)`.** For a prime `P ≥ 5`, `a ≥ 2` and a set `S` of proper
divisors of `2^a P`, the energy is maximal exactly when `2^a, 2^(a-1) P, 1 ∈ S`, `2^(a-1), P ∉ S`,
and for `1 ≤ k ≤ a - 2` exactly one of `2^k, 2^k P` lies in `S`, alternating in `k`. -/
theorem energy_eq_max_iff {P a : ℕ} (hP : P.Prime) (hP5 : 5 ≤ P) (ha : 2 ≤ a) {S : Finset ℕ}
    (hS : S ⊆ (2 ^ a * P).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) =
        Emax P a ↔
      2 ^ a ∈ S ∧ 2 ^ (a - 1) * P ∈ S ∧ 2 ^ (a - 1) ∉ S ∧ 1 ∈ S ∧ P ∉ S ∧
        (∀ k, 1 ≤ k → k ≤ a - 2 → (2 ^ k ∈ S ↔ 2 ^ k * P ∉ S)) ∧
        ∀ k, 1 ≤ k → k + 1 ≤ a - 2 → (2 ^ k ∈ S ↔ 2 ^ (k + 1) ∉ S) := by
  have hP5' : (5 : ℝ) ≤ P := by exact_mod_cast hP5
  set σ : ℕ → ℝ := fun k => zeta 2 a (Ys P S) k 0 with hσdef
  set τ : ℕ → ℝ := fun k => zeta 2 a (Ys P S) k 1 with hτdef
  have hz : ∀ k < a, Ys P S k 0 = 0 ∨ Ys P S k 0 = 1 := fun k _ => Ys_bit P S k 0
  have hw : ∀ k < a, Ys P S k 1 = 0 ∨ Ys P S k 1 = 1 := fun k _ => Ys_bit P S k 1
  have hσr : ∀ k < a, σ k = (σ (k + 1) + Ys P S k 0) / 2 := fun k hk => zeta_rec_two P S 0 hk
  have hτr : ∀ k < a, τ k = (τ (k + 1) + Ys P S k 1) / 2 := fun k hk => zeta_rec_two P S 1 hk
  have htop := not_mem_top hS
  have hτa : τ a = 0 := by simp only [hτdef, zeta_last, htop]
  have hσa : σ a = Ys P S a 0 := by simp only [hσdef, zeta_last]
  have hs01 : 0 ≤ σ a ∧ σ a ≤ 1 := by rw [hσa]; rcases Ys_bit P S a 0 with h | h <;> rw [h] <;> norm_num
  have hE := energy_eq_chain P a hP (by omega) S
  obtain ⟨-, hEmax⟩ := Wb_top hP5' (by omega : 1 ≤ a) (Or.inr rfl : (1 : ℝ) = 0 ∨ (1 : ℝ) = 1)
  have h2a : (0 : ℝ) < 2 ^ a := by positivity
  have hle := chain_le hP5' ha hz hw hσr hτr hs01.1 hs01.2 (by rw [hτa]) (by rw [hτa]; norm_num)
  set C := Fp P (σ 0) (τ 0) + ∑ k ∈ range a, Fp P (σ k - σ (k + 1)) (τ k - τ (k + 1)) with hCdef
  have hEC : ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * P) S) (ICGBridge.icgAdj_isHermitian _ _) =
      2 ^ a * C := hE
  have hEm : Emax P a = 2 ^ a * Wb P a 1 0 := by unfold Emax; rw [hEmax]
  rw [hEC, hEm]
  have key : 2 ^ a * C = 2 ^ a * Wb P a 1 0 ↔ Ys P S a 0 = 1 ∧ Wb P a (σ a) (τ a) ≤ C := by
    constructor
    · intro h
      have hC : C = Wb P a 1 0 := by
        have := mul_left_cancel₀ h2a.ne' h; exact this
      have hza : Ys P S a 0 = 1 := by
        rcases Ys_bit P S a 0 with h0 | h0
        · rw [hσa, h0, hτa] at hle
          exact absurd (hC ▸ hle) (not_le.2 (Wb_zero_lt hP5' ha))
        · exact h0
      refine ⟨hza, ?_⟩
      rw [hσa, hza, hτa, hC]
    · rintro ⟨hza, hge⟩
      rw [hσa, hza, hτa] at hle hge
      rw [le_antisymm hle hge]
  rw [key, chain_eq_iff hP5' ha hz hw hσr hτr hs01.1 hs01.2 (by rw [hτa]) (by rw [hτa]; norm_num)]
  constructor
  · rintro ⟨hza, hT, h00, h01⟩
    have hσ1 : σ a = 1 := by rw [hσa, hza]
    obtain ⟨hzA, hwA, hone, halt⟩ := (path_iff hP5' ha hz hw hσr hτr hσ1 hτa).1 hT
    refine ⟨(Ys_zero_iff P S a).1 hza, (Ys_one_iff P S (a - 1)).1 hwA,
      fun h => by rw [(Ys_zero_iff P S (a - 1)).2 h] at hzA; norm_num at hzA,
      by simpa using (Ys_zero_iff P S 0).1 h00,
      fun h => by
        have := (Ys_one_iff P S 0).2 (by simpa using h); rw [h01] at this; norm_num at this,
      fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
    · have := (bits_sum_one (Ys_bit P S k 0) (Ys_bit P S k 1)).1 (hone k h1 h2)
      rw [Ys_zero_iff, Ys_one_iff] at this; exact this
    · have := (bits_sum_one (Ys_bit P S k 0) (Ys_bit P S (k + 1) 0)).1 (halt k h1 h2)
      rw [Ys_zero_iff, Ys_zero_iff] at this; exact this
  · rintro ⟨hA, hA1, hA0, h1, hP1, hone, halt⟩
    have hza : Ys P S a 0 = 1 := (Ys_zero_iff P S a).2 hA
    have hσ1 : σ a = 1 := by rw [hσa, hza]
    refine ⟨hza, (path_iff hP5' ha hz hw hσr hτr hσ1 hτa).2 ⟨?_, (Ys_one_iff P S (a - 1)).2 hA1,
      fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩, (Ys_zero_iff P S 0).2 (by simpa using h1), ?_⟩
    · exact (bit_zero_iff (Ys_bit P S (a - 1) 0)).2 fun h => hA0 ((Ys_zero_iff P S (a - 1)).1 h)
    · refine (bits_sum_one (Ys_bit P S k 0) (Ys_bit P S k 1)).2 ?_
      rw [Ys_zero_iff, Ys_one_iff]; exact hone k h1 h2
    · refine (bits_sum_one (Ys_bit P S k 0) (Ys_bit P S (k + 1) 0)).2 ?_
      rw [Ys_zero_iff, Ys_zero_iff]; exact halt k h1 h2
    · exact (bit_zero_iff (Ys_bit P S 0 1)).2 fun h => hP1 (by simpa using (Ys_one_iff P S 0).1 h)

end Solved.ICG.TwoPow
