import Formal.ICG.MultiFamilies

/-!
# Order `2p²q` with `q < p`: which candidate maximises

`Families.energy_2_p2_q_gt` proves that for primes `3 ≤ q < p` the only possible maximisers of
`E(ICG(2p²q, S))` are `A = {1, 2, p², 2p², q, 2pq, p²q}` and `B = {1, p, 2p, 2p², 2q, p²q}`.
Here `E(A) - E(B) = 2(5p² - 6pq + 9q - 8)`, which is never zero, so exactly one of them is the
unique maximiser at each pair of primes, and which one depends on the primes.
-/

namespace Solved.ICG.Multi.Families

/-- `5p² - 6pq + 9q - 8` never vanishes at primes `3 ≤ q < p`: a zero would make `2p - 3`
divide `13`. -/
theorem ratio_ne_zero {p q : ℕ} (hp : p.Prime) (hq0 : 3 ≤ q) (hqp : q < p) :
    5 * p ^ 2 + 9 * q ≠ 6 * p * q + 8 := by
  intro h
  have hz : (5 * (p : ℤ) ^ 2 + 9 * q) = 6 * p * q + 8 := by exact_mod_cast h
  have h13 : (2 * (p : ℤ) - 3) * (12 * q - 10 * p - 15) = 13 := by linear_combination (-4) * hz
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  have ha : (7 : ℤ) ≤ 2 * p - 3 := by omega
  have hk : 0 < 12 * (q : ℤ) - 10 * p - 15 := by nlinarith
  have hk1 : 12 * (q : ℤ) - 10 * p - 15 = 1 := by nlinarith
  have h8 : p = 8 := by rw [hk1, mul_one] at h13; omega
  exact absurd (h8 ▸ hp) (by norm_num)

/-- Of two candidates, the one with the larger energy is the unique maximiser. -/
private theorem winner {S W L : Finset ℕ} {EW EL e : ℝ} (hlt : EL < EW)
    (hc : (S = W → e = EW) ∧ (S = L → e = EL) ∧ (S ≠ W → S ≠ L → e < EW ∨ e < EL)) :
    e ≤ EW ∧ (e = EW ↔ S = W) := by
  obtain ⟨hW, hL, hO⟩ := hc
  have key : S ≠ W → e < EW := fun hne => by
    by_cases hSL : S = L
    · rw [hL hSL]; exact hlt
    · rcases hO hne hSL with h | h
      · exact h
      · exact h.trans hlt
  refine ⟨?_, fun he => ?_, fun h => hW h⟩
  · by_cases hSW : S = W
    · exact (hW hSW).le
    · exact (key hSW).le
  · by_contra hne; exact absurd he (key hne).ne

/-- **`n = 2p²q`, `3 ≤ q < p`, `5p² + 9q > 6pq + 8`.** `A = {1, 2, p², 2p², q, 2pq, p²q}` is the
unique maximiser. -/
theorem energy_2_p2_q_gt_A {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq0 : 3 ≤ q) (hqp : q < p)
    (hD : 6 * p * q + 8 < 5 * p ^ 2 + 9 * q) {S : Finset ℕ}
    (hS : S ⊆ (2 * p ^ 2 * q).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 2 * q) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        -8 + 12 * (q : ℝ) + 16 * (p : ℝ) - 24 * (p : ℝ) * (q : ℝ) - 10 * (p : ℝ) ^ 2 +
          16 * (p : ℝ) ^ 2 * (q : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 2 * q) S) (ICGBridge.icgAdj_isHermitian _ _) =
          -8 + 12 * (q : ℝ) + 16 * (p : ℝ) - 24 * (p : ℝ) * (q : ℝ) - 10 * (p : ℝ) ^ 2 +
            16 * (p : ℝ) ^ 2 * (q : ℝ) ↔
        S = {1, 2, p ^ 2, 2 * p ^ 2, q, 2 * p * q, p ^ 2 * q}) := by
  obtain ⟨hA, hB, hO⟩ := energy_2_p2_q_gt hp hq hq0 hqp hS
  have hD' : (6 * p * q + 8 : ℝ) < 5 * p ^ 2 + 9 * q := by exact_mod_cast hD
  exact winner (by nlinarith) ⟨hA, hB, hO⟩

/-- **`n = 2p²q`, `3 ≤ q < p`, `5p² + 9q < 6pq + 8`.** `B = {1, p, 2p, 2p², 2q, p²q}` is the
unique maximiser. -/
theorem energy_2_p2_q_gt_B {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq0 : 3 ≤ q) (hqp : q < p)
    (hD : 5 * p ^ 2 + 9 * q < 6 * p * q + 8) {S : Finset ℕ}
    (hS : S ⊆ (2 * p ^ 2 * q).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 2 * q) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        8 - 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) - 20 * (p : ℝ) ^ 2 +
          16 * (p : ℝ) ^ 2 * (q : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 2 * q) S) (ICGBridge.icgAdj_isHermitian _ _) =
          8 - 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) - 20 * (p : ℝ) ^ 2 +
            16 * (p : ℝ) ^ 2 * (q : ℝ) ↔
        S = {1, p, 2 * p, 2 * p ^ 2, 2 * q, p ^ 2 * q}) := by
  obtain ⟨hA, hB, hO⟩ := energy_2_p2_q_gt hp hq hq0 hqp hS
  have hD' : (5 * p ^ 2 + 9 * q : ℝ) < 6 * p * q + 8 := by exact_mod_cast hD
  exact winner (by nlinarith) ⟨hB, hA, fun h1 h2 => (hO h2 h1).symm⟩

end Solved.ICG.Multi.Families
