import Formal.ICG.TwoPb.Attain
import Formal.ICG.EvenFamilies

/-!
# `max_S E(ICG(2 p^b, S))` for every `b ≥ 1`

`energy_max_all` joins `energy_max` (`b ≥ 2`) with the certified family `energy_1_1` (`b = 1`):
for every odd prime `p` and every `b ≥ 1` the maximum is `2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`,
attained by `setP p b (zOpt b) (wOpt b)`.

`closed_form_eq_family` checks the closed form against the independently certified polynomials of
`energy_1_b` (`EvenFamilies.lean`, branch-and-bound certificates) for `b = 1, …, 7`.
-/

noncomputable section

open Finset

namespace Solved.ICG.TwoPb

/-- The closed form `2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`. -/
def Emax2pb (p : ℝ) (b : ℕ) : ℝ := 2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * p ^ (b - j)

theorem closed_form_eq_family (p : ℝ) :
    Emax2pb p 1 = -2 + 4 * p ∧
    Emax2pb p 2 = -2 - 4 * p + 6 * p ^ 2 ∧
    Emax2pb p 3 = 2 - 4 * p - 6 * p ^ 2 + 8 * p ^ 3 ∧
    Emax2pb p 4 = 2 + 4 * p - 6 * p ^ 2 - 8 * p ^ 3 + 10 * p ^ 4 ∧
    Emax2pb p 5 = -2 + 4 * p + 6 * p ^ 2 - 8 * p ^ 3 - 10 * p ^ 4 + 12 * p ^ 5 ∧
    Emax2pb p 6 = -2 - 4 * p + 6 * p ^ 2 + 8 * p ^ 3 - 10 * p ^ 4 - 12 * p ^ 5 + 14 * p ^ 6 ∧
    Emax2pb p 7 = 2 - 4 * p - 6 * p ^ 2 + 8 * p ^ 3 + 10 * p ^ 4 - 12 * p ^ 5 - 14 * p ^ 6 +
      16 * p ^ 7 := by
  simp only [Emax2pb, sum_range_succ, sum_range_zero, eps]
  norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem setP_one {p : ℕ} : setP p 1 (zOpt 1) (wOpt 1) = {2 ^ 0 * p ^ 0, 2 ^ 0 * p ^ 1, 2 ^ 1 * p ^ 0} := by
  have hz : zOpt 1 0 = 1 := by simp [zOpt, cycZ]
  have hw : wOpt 1 0 = 1 := by simp [wOpt, cycW]
  ext d
  simp only [setP, mem_insert, mem_union, mem_image, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro (rfl | ⟨k, ⟨hk, -⟩, rfl⟩ | ⟨k, ⟨hk, -⟩, rfl⟩)
    · right; left; ring
    · obtain rfl : k = 0 := by omega
      left; ring
    · obtain rfl : k = 0 := by omega
      right; right; ring
  · rintro (rfl | rfl | rfl)
    · right; left; exact ⟨0, ⟨by norm_num, hz⟩, by ring⟩
    · left; ring
    · right; right; exact ⟨0, ⟨by norm_num, hw⟩, by ring⟩

/-- **The maximal energy of `ICG(2 p^b, S)` for every `b ≥ 1`.** For every odd prime `p` and every
`b ≥ 1`, every divisor set `S` gives `E(ICG(2 p^b, S)) ≤ 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`
(`ε = (1, -1, -1, 1)` repeating), with equality for `S = setP p b (zOpt b) (wOpt b)`. -/
theorem energy_max_all {p b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hb : 1 ≤ b) :
    (∀ S ⊆ (2 * p ^ b).properDivisors,
      ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        Emax2pb p b) ∧
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ b) (setP p b (zOpt b) (wOpt b)))
        (ICGBridge.icgAdj_isHermitian _ _) = Emax2pb p b := by
  rcases Nat.lt_or_ge b 2 with h | h
  · obtain rfl : b = 1 := by omega
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hn : 2 * p ^ 1 = 2 ^ 1 * p ^ 1 := by ring
    have hv := (closed_form_eq_family (p : ℝ)).1
    refine ⟨fun S hS => ?_, ?_⟩
    · rw [hn] at hS ⊢
      rw [hv]
      exact (Solved.ICG.Families.energy_1_1 hp hp3 hS).1
    · have hS := setP_sub hp (b := 1) (zOpt 1) (wOpt 1)
      rw [hn] at hS ⊢
      rw [hv]
      exact (Solved.ICG.Families.energy_1_1 hp hp3 hS).2.2 (setP_one)
  · exact energy_max hp hp2 h

end Solved.ICG.TwoPb
