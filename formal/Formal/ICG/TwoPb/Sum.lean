import Mathlib

/-!
# The closed form of `S(b) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) x^j`

`ε = (1, -1, -1, 1)` repeating with period 4 is the coefficient sequence of
`E(x) = (1 - x)/(1 + x^2)`. With `g = 2E` this file proves, for every real `x`,

`S(b) = b g + α + x^b β_{b mod 4}`,  `α = 2(1 + 3x^2 - 2x^3)/(1 + x^2)^2`,

from `∑_{j ≤ m} ε_j x^j = E - x^{m+1} R_{(m+1) mod 4}` and `S(b+1) = S(b) + 2 ∑_{j ≤ b+1} ε_j x^j`, and
rewrites `p^b S(b)` at `x = 1/p` as the integer polynomial `2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`.
-/

open Finset

noncomputable section

namespace Solved.ICG.TwoPb

/-- `ε_j = 1, -1, -1, 1` for `j ≡ 0, 1, 2, 3 (mod 4)`. -/
def eps (j : ℕ) : ℝ := if j % 4 = 0 ∨ j % 4 = 3 then 1 else -1

/-- `E(x) = (1 - x)/(1 + x^2) = ∑ ε_j x^j`. -/
def Einf (x : ℝ) : ℝ := (1 - x) / (x ^ 2 + 1)

/-- `g = 2(1 - x)/(1 + x^2)`, the gain per step. -/
def gS (x : ℝ) : ℝ := 2 * (1 - x) / (x ^ 2 + 1)

/-- `R_k(x) = ∑_{i ≥ 0} ε_{k+i} x^i`. -/
def Rr (x : ℝ) (k : ℕ) : ℝ :=
  if k % 4 = 0 then (1 - x) / (x ^ 2 + 1) else if k % 4 = 1 then -(x + 1) / (x ^ 2 + 1)
  else if k % 4 = 2 then (x - 1) / (x ^ 2 + 1) else (x + 1) / (x ^ 2 + 1)

/-- `α = 2(1 + 3x^2 - 2x^3)/(1 + x^2)^2`. -/
def alphaS (x : ℝ) : ℝ := 2 * (1 + 3 * x ^ 2 - 2 * x ^ 3) / (x ^ 2 + 1) ^ 2

/-- `β_k`: `S(b) - b g - α = x^b β_{b mod 4}`. -/
def betaS (x : ℝ) (k : ℕ) : ℝ :=
  if k % 4 = 0 then 2 * x ^ 2 * (x ^ 2 + 2 * x - 1) / (x ^ 2 + 1) ^ 2
  else if k % 4 = 1 then -2 * x ^ 2 * (x ^ 2 - 2 * x - 1) / (x ^ 2 + 1) ^ 2
  else if k % 4 = 2 then -2 * x ^ 2 * (x ^ 2 + 2 * x - 1) / (x ^ 2 + 1) ^ 2
  else 2 * x ^ 2 * (x ^ 2 - 2 * x - 1) / (x ^ 2 + 1) ^ 2

/-- `∑_{j ≤ m} ε_j x^j`. -/
def Esum (x : ℝ) (m : ℕ) : ℝ := ∑ j ∈ range (m + 1), eps j * x ^ j

/-- `S(b) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) x^j`. -/
def Ssum (x : ℝ) (b : ℕ) : ℝ := 2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * x ^ j

theorem mod4_cases (j : ℕ) : j % 4 = 0 ∨ j % 4 = 1 ∨ j % 4 = 2 ∨ j % 4 = 3 := by omega

theorem Rr_rec (x : ℝ) (j : ℕ) : Rr x j - x * Rr x (j + 1) = eps j := by
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  rcases mod4_cases j with h | h | h | h <;>
  · have h' : (j + 1) % 4 = (j % 4 + 1) % 4 := by omega
    simp only [Rr, eps, h, h']
    norm_num
    field_simp
    ring

theorem betaS_rec (x : ℝ) (k : ℕ) :
    x * betaS x (k + 1) - betaS x k + 2 * x ^ 2 * Rr x (k + 2) = 0 := by
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  rcases mod4_cases k with h | h | h | h <;>
  · have h1 : (k + 1) % 4 = (k % 4 + 1) % 4 := by omega
    have h2 : (k + 2) % 4 = (k % 4 + 2) % 4 := by omega
    simp only [betaS, Rr, h, h1, h2]
    norm_num
    field_simp
    ring

theorem Esum_closed (x : ℝ) (m : ℕ) : Esum x m = Einf x - x ^ (m + 1) * Rr x (m + 1) := by
  induction m with
  | zero =>
    have hx : x ^ 2 + 1 ≠ 0 := by positivity
    simp only [Esum, Einf, Rr, eps]
    norm_num
    field_simp
    ring
  | succ m ih =>
    have hr := Rr_rec x (m + 1)
    rw [Esum, sum_range_succ, ← Esum, ih]
    have e : x ^ (m + 1 + 1) * Rr x (m + 1 + 1) = x ^ (m + 1) * (x * Rr x (m + 1 + 1)) := by ring
    rw [e, show x * Rr x (m + 1 + 1) = Rr x (m + 1) - eps (m + 1) by linarith]
    ring

theorem Ssum_succ (x : ℝ) (b : ℕ) : Ssum x (b + 1) = Ssum x b + 2 * Esum x (b + 1) := by
  unfold Ssum Esum
  have h : ∑ j ∈ range (b + 1 + 1), eps j * (((b + 1 : ℕ) : ℝ) + 1 - j) * x ^ j =
      ∑ j ∈ range (b + 1 + 1), eps j * ((b : ℝ) + 1 - j) * x ^ j +
        ∑ j ∈ range (b + 1 + 1), eps j * x ^ j := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast; ring
  rw [h, sum_range_succ (fun j => eps j * ((b : ℝ) + 1 - j) * x ^ j)]
  push_cast
  ring

theorem Ssum_closed (x : ℝ) (b : ℕ) : Ssum x b = b * gS x + alphaS x + x ^ b * betaS x b := by
  have hx : x ^ 2 + 1 ≠ 0 := by positivity
  induction b with
  | zero =>
    simp only [Ssum, alphaS, betaS, eps]
    norm_num
    field_simp
    ring
  | succ b ih =>
    rw [Ssum_succ, ih, Esum_closed]
    have hb := betaS_rec x b
    have e : x ^ (b + 1) * betaS x (b + 1) = x ^ b * (x * betaS x (b + 1)) := by ring
    rw [e, show x * betaS x (b + 1) = betaS x b - 2 * x ^ 2 * Rr x (b + 2) by linarith]
    unfold gS Einf
    push_cast
    field_simp
    ring

/-- At `x = 1/p`: `p^b S(b) = 2 ∑_{j ≤ b} ε_j (b + 1 - j) p^(b - j)`. -/
theorem Ssum_eq_poly {p : ℝ} (hp : p ≠ 0) (b : ℕ) :
    p ^ b * Ssum (1 / p) b = 2 * ∑ j ∈ range (b + 1), eps j * ((b : ℝ) + 1 - j) * p ^ (b - j) := by
  unfold Ssum
  rw [mul_left_comm, mul_sum]
  congr 1
  refine sum_congr rfl fun j hj => ?_
  have hj' : j ≤ b := Nat.lt_succ_iff.1 (mem_range.1 hj)
  rw [one_div, inv_pow, pow_sub₀ p hp hj']
  ring

end Solved.ICG.TwoPb
