import Formal.ICG.MultiFamilies

/-!
# Orders `2p²q` and `2p³q` with `q < p`: which candidate maximises

`Families.energy_2_p2_q_gt` proves that for primes `3 ≤ q < p` the only possible maximisers of
`E(ICG(2p²q, S))` are `A = {1, 2, p², 2p², q, 2pq, p²q}` and `B = {1, p, 2p, 2p², 2q, p²q}`.
Here `E(A) - E(B) = 2(5p² - 6pq + 9q - 8)`, which is never zero, so exactly one of them is the
unique maximiser at each pair of primes, and which one depends on the primes.

For `2p³q`, `Families.energy_2_p3_q_gt` gives four candidates; three of them share one energy
`E₁`, and `E₁ - E₂ = 2(7p³ - 9p²q + 18pq - 16p - 9q + 8)`, again never zero.
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

/-- `7p³ - 9p²q + 18pq - 16p - 9q + 8` never vanishes at primes `3 ≤ q < p`: a zero would give
`(p - 1)(9q(p - 1) - 7p² - 7p + 9) = -1` with `p - 1 ≥ 3`. -/
theorem ratio3_ne_zero {q p : ℕ} (hq0 : 3 ≤ q) (hqp : q < p) :
    7 * p ^ 3 + 18 * p * q + 8 ≠ 9 * p ^ 2 * q + 16 * p + 9 * q := by
  intro h
  have hz : (7 * (p : ℤ) ^ 3 + 18 * p * q + 8) = 9 * p ^ 2 * q + 16 * p + 9 * q := by
    exact_mod_cast h
  have h1 : ((p : ℤ) - 1) * (9 * q * (p - 1) - 7 * p ^ 2 - 7 * p + 9) = -1 := by
    linear_combination (-1) * hz
  have ha : (3 : ℤ) ≤ p - 1 := by omega
  have hk : 9 * (q : ℤ) * (p - 1) - 7 * p ^ 2 - 7 * p + 9 < 0 := by nlinarith
  nlinarith

/-- Of candidates where one energy `EW` is shared by a group and beats the other energy `EL`,
the group is exactly the set of maximisers. -/
private theorem winner_group {S W₁ W₂ W₃ L : Finset ℕ} {EW EL e : ℝ} (hlt : EL < EW)
    (h₁ : S = W₁ → e = EW) (hL : S = L → e = EL) (h₂ : S = W₂ → e = EW) (h₃ : S = W₃ → e = EW)
    (hO : S ≠ W₁ → S ≠ L → S ≠ W₂ → S ≠ W₃ → e < EW ∨ e < EL ∨ e < EW ∨ e < EW) :
    e ≤ EW ∧ (e = EW ↔ S = W₁ ∨ S = W₂ ∨ S = W₃) := by
  have key : ¬(S = W₁ ∨ S = W₂ ∨ S = W₃) → e < EW := fun hne => by
    push Not at hne
    obtain ⟨n₁, n₂, n₃⟩ := hne
    by_cases hSL : S = L
    · rw [hL hSL]; exact hlt
    · rcases hO n₁ hSL n₂ n₃ with h | h | h | h
      · exact h
      · exact h.trans hlt
      · exact h
      · exact h
  refine ⟨?_, fun he => ?_, fun h => ?_⟩
  · by_cases hW : S = W₁ ∨ S = W₂ ∨ S = W₃
    · rcases hW with h | h | h
      · exact (h₁ h).le
      · exact (h₂ h).le
      · exact (h₃ h).le
    · exact (key hW).le
  · by_contra hne; exact absurd he (key hne).ne
  · rcases h with h | h | h
    · exact h₁ h
    · exact h₂ h
    · exact h₃ h

/-- **`n = 2p³q`, `3 ≤ q < p`, `7p³ + 18pq + 8 > 9p²q + 16p + 9q`.** The maximisers are exactly
`{1, 2p, p², 2p³, q, 2q, p²q, 2p²q}`, `{1, 2, p², 2p², 2q, pq, 2p²q, p³q}` and
`{2, p, 2p², p³, q, 2q, p²q, 2p²q}`. -/
theorem energy_2_p3_q_gt_A {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq0 : 3 ≤ q) (hqp : q < p)
    (hD : 9 * p ^ 2 * q + 16 * p + 9 * q < 7 * p ^ 3 + 18 * p * q + 8) {S : Finset ℕ}
    (hS : S ⊆ (2 * p ^ 3 * q).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 3 * q) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        8 - 12 * (q : ℝ) - 16 * (p : ℝ) + 24 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
          36 * (p : ℝ) ^ 2 * (q : ℝ) - 14 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 3 * q) S) (ICGBridge.icgAdj_isHermitian _ _) =
          8 - 12 * (q : ℝ) - 16 * (p : ℝ) + 24 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
            36 * (p : ℝ) ^ 2 * (q : ℝ) - 14 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) ↔
        S = {1, 2 * p, p ^ 2, 2 * p ^ 3, q, 2 * q, p ^ 2 * q, 2 * p ^ 2 * q} ∨
          S = {1, 2, p ^ 2, 2 * p ^ 2, 2 * q, p * q, 2 * p ^ 2 * q, p ^ 3 * q} ∨
          S = {2, p, 2 * p ^ 2, p ^ 3, q, 2 * q, p ^ 2 * q, 2 * p ^ 2 * q}) := by
  obtain ⟨h₁, hL, h₂, h₃, hO⟩ := energy_2_p3_q_gt hp hq hq0 hqp hS
  have hD' : (9 * p ^ 2 * q + 16 * p + 9 * q : ℝ) < 7 * p ^ 3 + 18 * p * q + 8 := by
    exact_mod_cast hD
  exact winner_group (by nlinarith) h₁ hL h₂ h₃ hO

/-- **`n = 2p³q`, `3 ≤ q < p`, `7p³ + 18pq + 8 < 9p²q + 16p + 9q`.**
`{1, 2, p, 2p³, 2pq, p²q, 2p²q, p³q}` is the unique maximiser. -/
theorem energy_2_p3_q_gt_B {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hq0 : 3 ≤ q) (hqp : q < p)
    (hD : 7 * p ^ 3 + 18 * p * q + 8 < 9 * p ^ 2 * q + 16 * p + 9 * q) {S : Finset ℕ}
    (hS : S ⊆ (2 * p ^ 3 * q).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 3 * q) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        -8 + 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
          18 * (p : ℝ) ^ 2 * (q : ℝ) - 28 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 3 * q) S) (ICGBridge.icgAdj_isHermitian _ _) =
          -8 + 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
            18 * (p : ℝ) ^ 2 * (q : ℝ) - 28 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) ↔
        S = {1, 2, p, 2 * p ^ 3, 2 * p * q, p ^ 2 * q, 2 * p ^ 2 * q, p ^ 3 * q}) := by
  obtain ⟨h₁, hB, h₂, h₃, hO⟩ := energy_2_p3_q_gt hp hq hq0 hqp hS
  have hD' : (7 * p ^ 3 + 18 * p * q + 8 : ℝ) < 9 * p ^ 2 * q + 16 * p + 9 * q := by
    exact_mod_cast hD
  have hlt : 8 - 12 * (q : ℝ) - 16 * (p : ℝ) + 24 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
      36 * (p : ℝ) ^ 2 * (q : ℝ) - 14 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) <
      -8 + 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
        18 * (p : ℝ) ^ 2 * (q : ℝ) - 28 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) := by
    nlinarith
  have key : S ≠ {1, 2, p, 2 * p ^ 3, 2 * p * q, p ^ 2 * q, 2 * p ^ 2 * q, p ^ 3 * q} →
      ICGBridge.energy (ICGBridge.icgAdj (2 * p ^ 3 * q) S) (ICGBridge.icgAdj_isHermitian _ _) <
        -8 + 6 * (q : ℝ) + 16 * (p : ℝ) - 12 * (p : ℝ) * (q : ℝ) + 24 * (p : ℝ) ^ 2 -
          18 * (p : ℝ) ^ 2 * (q : ℝ) - 28 * (p : ℝ) ^ 3 + 22 * (p : ℝ) ^ 3 * (q : ℝ) := by
    intro hne
    by_cases e₁ : S = {1, 2 * p, p ^ 2, 2 * p ^ 3, q, 2 * q, p ^ 2 * q, 2 * p ^ 2 * q}
    · rw [h₁ e₁]; exact hlt
    by_cases e₂ : S = {1, 2, p ^ 2, 2 * p ^ 2, 2 * q, p * q, 2 * p ^ 2 * q, p ^ 3 * q}
    · rw [h₂ e₂]; exact hlt
    by_cases e₃ : S = {2, p, 2 * p ^ 2, p ^ 3, q, 2 * q, p ^ 2 * q, 2 * p ^ 2 * q}
    · rw [h₃ e₃]; exact hlt
    rcases hO e₁ hne e₂ e₃ with h | h | h | h
    · exact h.trans hlt
    · exact h
    · exact h.trans hlt
    · exact h.trans hlt
  refine ⟨?_, fun he => ?_, fun h => hB h⟩
  · by_cases hSB : S = {1, 2, p, 2 * p ^ 3, 2 * p * q, p ^ 2 * q, 2 * p ^ 2 * q, p ^ 3 * q}
    · exact (hB hSB).le
    · exact (key hSB).le
  · by_contra hne; exact absurd he (key hne).ne

end Solved.ICG.Multi.Families
