import Formal.ICG.TwoPb.Steps
import Formal.ICG.TwoPb.Start
import Formal.ICG.TwoPb.Sum
import Formal.ICG.TwoPb.Bridge

/-!
# The value function of the `2p^b` chain and the upper bound

Fix `y ≥ 0` and `x = 1/(y + 3)`. For `n ≥ 1` steps left the value function is bounded by
`W_n(s, t) = n Kg + Mx_{n mod 4}(τ_n; s, t) (× 1/K)`, `τ_n = x^(n - m_n)` with `m_n ∈ {4, 1, 2, 3}` the least
`n' ≥ 1`, `n' ≡ n (mod 4)` (`Formal/ICG/TwoPb/Pieces.lean`). One step (`step_W`) is the generated
`step_k`; the last step (`base_W`) is `base_any`. Induction along the bridge path (`chain_le`) and the start
bound (`start_W`, from `start_k` and `Ssum_closed`) give
`E(ICG(2 p^b, S)) ≤ p^b S(b) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)` for every `b ≥ 2` (`energy_le`).
-/

noncomputable section

open Finset ICGGeneral

namespace Solved.ICG.TwoPb

/-- `m_n`: the least `n' ≥ 1` with `n' ≡ n (mod 4)`. -/
def mk (n : ℕ) : ℕ := if n % 4 = 0 then 4 else n % 4

/-- `τ_n = x^(n - m_n)`, `x = 1/(y + 3)`. -/
def tauN (y : ℝ) (n : ℕ) : ℝ := (1 / (y + 3)) ^ (n - mk n)

/-- The maximum of the residue-`(n mod 4)` pieces. -/
def MxN (n : ℕ) (y τ s t : ℝ) : ℝ :=
  if n % 4 = 0 then Mx_0 y τ s t else if n % 4 = 1 then Mx_1 y τ s t
  else if n % 4 = 2 then Mx_2 y τ s t else Mx_3 y τ s t

/-- `K W_n(s, t)`. -/
def Wh (y : ℝ) (n : ℕ) (s t : ℝ) : ℝ := n * Kg y + MxN n y (tauN y n) s t

theorem MxN_0 {n : ℕ} (h : n % 4 = 0) (y τ s t : ℝ) : MxN n y τ s t = Mx_0 y τ s t := by
  simp [MxN, h]

theorem MxN_1 {n : ℕ} (h : n % 4 = 1) (y τ s t : ℝ) : MxN n y τ s t = Mx_1 y τ s t := by
  simp [MxN, h]

theorem MxN_2 {n : ℕ} (h : n % 4 = 2) (y τ s t : ℝ) : MxN n y τ s t = Mx_2 y τ s t := by
  simp [MxN, h]

theorem MxN_3 {n : ℕ} (h : n % 4 = 3) (y τ s t : ℝ) : MxN n y τ s t = Mx_3 y τ s t := by
  simp [MxN, h]

theorem Kc_pos {y : ℝ} (hy : 0 ≤ y) : 0 < Kc y := by unfold Kc; positivity

theorem Kgain_eq {y : ℝ} (hy : 0 ≤ y) : Kgain y = Kc y * (2 * (y + 2) / (y + 3)) := by
  have : y + 3 ≠ 0 := by positivity
  unfold Kgain Kc; field_simp; ring

theorem Kg_eq {y : ℝ} (hy : 0 ≤ y) : Kg y = Kc y * gS (1 / (y + 3)) := by
  have : y + 3 ≠ 0 := by positivity
  unfold Kg Kc gS; field_simp; ring

theorem tauN_nonneg {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : 0 ≤ tauN y n := by unfold tauN; positivity

theorem x_le_one {y : ℝ} (hy : 0 ≤ y) : 1 / (y + 3) ≤ 1 := by
  rw [div_le_one (by positivity)]; linarith

theorem tauN_le_one {y : ℝ} (hy : 0 ≤ y) (n : ℕ) : tauN y n ≤ 1 :=
  pow_le_one₀ (by positivity) (x_le_one hy)

theorem tauN_succ_0 {y : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : 1 ≤ n) (h : n % 4 = 0) :
    (y + 3) ^ 4 * tauN y (n + 1) = tauN y n := by
  have hm : mk n = 4 := by simp [mk, h]
  have hm1 : mk (n + 1) = 1 := by unfold mk; split_ifs <;> omega
  have h4 : 4 ≤ n := by omega
  unfold tauN
  rw [hm, hm1, Nat.add_sub_cancel, show n = n - 4 + 4 by omega, Nat.add_sub_cancel, pow_add]
  have : y + 3 ≠ 0 := by positivity
  field_simp

theorem tauN_succ {y : ℝ} {n : ℕ} (hn : 1 ≤ n) (h : n % 4 ≠ 0) : tauN y (n + 1) = tauN y n := by
  unfold tauN mk
  congr 1
  split_ifs <;> omega

/-- `K F₂(s' - s, t' - t) = max(Kgain |z - s|, Kgain |w - t|)` for one step to the corner `(z, w)`. -/
theorem KF2 {y s t s' t' z w : ℝ} (hy : 0 ≤ y) (hs' : (y + 3) * s' = s + (y + 2) * z)
    (ht' : (y + 3) * t' = t + (y + 2) * w) :
    Kc y * F2 (s' - s) (t' - t) = max (Kgain y * |z - s|) (Kgain y * |w - t|) := by
  have h3 : 0 < y + 3 := by linarith
  have es : s' - s = (y + 2) / (y + 3) * (z - s) := by field_simp; linarith
  have et : t' - t = (y + 2) / (y + 3) * (w - t) := by field_simp; linarith
  have hc : 0 ≤ (y + 2) / (y + 3) := by positivity
  have hk : 0 ≤ Kc y * (2 * (y + 2) / (y + 3)) := mul_nonneg (Kc_pos hy).le (by positivity)
  rw [F2_eq, es, et, abs_mul, abs_mul, abs_of_nonneg hc, ← mul_max_of_nonneg _ _ hc, Kgain_eq hy,
    ← mul_max_of_nonneg _ _ hk]
  ring

/-- One step of the chain. -/
theorem step_W {y s t s' t' z w : ℝ} (hy : 0 ≤ y) {n : ℕ} (hn : 1 ≤ n) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1)
    (hs' : (y + 3) * s' = s + (y + 2) * z) (ht' : (y + 3) * t' = t + (y + 2) * w) :
    Kc y * F2 (s' - s) (t' - t) + Wh y n s' t' ≤ Wh y (n + 1) s t := by
  rw [KF2 hy hs' ht']
  unfold Wh
  have h0 := tauN_nonneg hy n
  have h1 := tauN_le_one hy n
  push_cast
  rcases mod4_cases n with h | h | h | h
  · rw [MxN_0 h, MxN_1 (by omega)]
    have := step_0 hy h0 h1 hs0 hs1 ht0 ht1 hz hw hs' ht' (tauN_succ_0 hy hn h)
    linarith
  · rw [MxN_1 h, MxN_2 (by omega), tauN_succ hn (by omega)]
    have := step_1 hy h0 h1 hs0 hs1 ht0 ht1 hz hw hs' ht' rfl
    linarith
  · rw [MxN_2 h, MxN_3 (by omega), tauN_succ hn (by omega)]
    have := step_2 hy h0 h1 hs0 hs1 ht0 ht1 hz hw hs' ht' rfl
    linarith
  · rw [MxN_3 h, MxN_0 (by omega), tauN_succ hn (by omega)]
    have := step_3 hy h0 h1 hs0 hs1 ht0 ht1 hz hw hs' ht' rfl
    linarith

/-- The last step, to the terminal value `F₂(s', t')`. -/
theorem base_W {y s t s' t' z w : ℝ} (hy : 0 ≤ y) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (hz : z = 0 ∨ z = 1) (hw : w = 0 ∨ w = 1)
    (hs' : (y + 3) * s' = s + (y + 2) * z) (ht' : (y + 3) * t' = t + (y + 2) * w) :
    Kc y * (F2 (s' - s) (t' - t) + F2 s' t') ≤ Wh y 1 s t := by
  have h3 : 0 < y + 3 := by linarith
  have hz0 : 0 ≤ z := by rcases hz with rfl | rfl <;> norm_num
  have hw0 : 0 ≤ w := by rcases hw with rfl | rfl <;> norm_num
  have hs'0 : 0 ≤ s' := by
    have : 0 ≤ (y + 3) * s' := by rw [hs']; positivity
    exact nonneg_of_mul_nonneg_right' h3 this
  have ht'0 : 0 ≤ t' := by
    have : 0 ≤ (y + 3) * t' := by rw [ht']; positivity
    exact nonneg_of_mul_nonneg_right' h3 this
  have hK := Kc_pos hy
  have hterm : Kc y * F2 s' t' = max (2 * Kc y * s') (2 * Kc y * t') := by
    rw [F2_eq, abs_of_nonneg hs'0, abs_of_nonneg ht'0, ← mul_max_of_nonneg _ _ (by positivity :
      (0 : ℝ) ≤ 2 * Kc y)]
    ring
  rw [mul_add, KF2 hy hs' ht', hterm]
  have hτ : tauN y 1 = 1 := by simp [tauN, mk]
  unfold Wh
  rw [MxN_1 (by norm_num), hτ]
  have := base_any hy hs0 hs1 ht0 ht1 hz hw hs' ht'
  push_cast
  linarith

/-- A step to a corner stays in the unit square. -/
theorem step_box {y u u' z : ℝ} (hy : 0 ≤ y) (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hz : z = 0 ∨ z = 1)
    (h : (y + 3) * u' = u + (y + 2) * z) : 0 ≤ u' ∧ u' ≤ 1 := by
  have h3 : 0 < y + 3 := by linarith
  rcases hz with rfl | rfl
  · constructor <;> nlinarith
  · constructor <;> nlinarith

/-- **The chain bound.** For a path `σ, τ` of length `b ≥ 1` driven by bits `z, w`, starting in the unit
square, `K (F₂(σ₀, τ₀) + ∑_{k<b} F₂(σ_k - σ_{k+1}, τ_k - τ_{k+1})) ≤ K W_b(σ_b, τ_b)`. -/
theorem chain_le {y : ℝ} (hy : 0 ≤ y) {b : ℕ} (hb : 1 ≤ b) {σ τ z w : ℕ → ℝ}
    (hz : ∀ k < b, z k = 0 ∨ z k = 1) (hw : ∀ k < b, w k = 0 ∨ w k = 1)
    (hσ : ∀ k < b, (y + 3) * σ k = σ (k + 1) + (y + 2) * z k)
    (hτ : ∀ k < b, (y + 3) * τ k = τ (k + 1) + (y + 2) * w k)
    (hσb : 0 ≤ σ b ∧ σ b ≤ 1) (hτb : 0 ≤ τ b ∧ τ b ≤ 1) :
    Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range b, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) ≤
      Wh y b (σ b) (τ b) := by
  -- every state is in the unit square
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
  -- induction on the number of steps
  have main : ∀ n, 1 ≤ n → n ≤ b →
      Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range n, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) ≤
        Wh y n (σ n) (τ n) := by
    intro n hn hnb
    induction n with
    | zero => omega
    | succ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hpos
      · obtain ⟨⟨a0, a1⟩, ⟨c0, c1⟩⟩ := boxk 1 hnb
        have := base_W hy a0 a1 c0 c1 (hz 0 (by omega)) (hw 0 (by omega)) (hσ 0 (by omega))
          (hτ 0 (by omega))
        simp only [range_one, sum_singleton, zero_add]
        linarith
      · have ih' := ih hpos (by omega)
        obtain ⟨⟨a0, a1⟩, ⟨c0, c1⟩⟩ := boxk (n + 1) hnb
        have := step_W hy hpos a0 a1 c0 c1 (hz n (by omega)) (hw n (by omega)) (hσ n (by omega))
          (hτ n (by omega))
        have e : Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range (n + 1), F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) =
            Kc y * (F2 (σ 0) (τ 0) + ∑ k ∈ range n, F2 (σ k - σ (k + 1)) (τ k - τ (k + 1))) +
              Kc y * F2 (σ n - σ (n + 1)) (τ n - τ (n + 1)) := by
          rw [sum_range_succ]; ring
        rw [e]
        linarith
  exact main b hb le_rfl

end Solved.ICG.TwoPb
