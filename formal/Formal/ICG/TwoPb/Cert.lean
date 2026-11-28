import Mathlib

/-!
# Elementary lemmas for the generated `2p^b` step certificates

The generated modules (`Formal/ICG/TwoPb/Pieces.lean`, `Step*.lean`, `Base.lean`, written by
`solved/lean_two_pb.py`) prove each candidate inequality as follows: one polynomial identity
`E (∑ N_l Q_l - M c) = A + B s + C t`, nonnegativity of the four corner values `A, A+B, A+C, A+B+C`,
then `aff_nonneg` on the unit square and `nonneg_of_mul_nonneg_right'` to divide by `E > 0`.
-/

namespace Solved.ICG.TwoPb

/-- An affine function of `(s, t)` that is nonnegative at the four corners of the unit square is
nonnegative on the square. -/
theorem aff_nonneg {s t A B C : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h00 : 0 ≤ A) (h10 : 0 ≤ A + B) (h01 : 0 ≤ A + C) (h11 : 0 ≤ A + B + C) :
    0 ≤ A + B * s + C * t := by
  have key : A + B * s + C * t = (1 - s) * (1 - t) * A + s * (1 - t) * (A + B) +
      (1 - s) * t * (A + C) + s * t * (A + B + C) := by ring
  rw [key]
  have hs : 0 ≤ 1 - s := by linarith
  have ht : 0 ≤ 1 - t := by linarith
  have := mul_nonneg (mul_nonneg hs ht) h00
  have := mul_nonneg (mul_nonneg hs0 ht) h10
  have := mul_nonneg (mul_nonneg hs ht0) h01
  have := mul_nonneg (mul_nonneg hs0 ht0) h11
  linarith

/-- An affine function of `τ` that is nonnegative at `τ = 0` and `τ = 1` is nonnegative on `[0, 1]`. -/
theorem lin_tau {τ p q : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hp : 0 ≤ p) (hpq : 0 ≤ p + q) :
    0 ≤ p + q * τ := by
  nlinarith [mul_nonneg h0 hpq, mul_nonneg (sub_nonneg.2 h1) hp]

/-- Dividing a nonnegative product by a positive factor. -/
theorem nonneg_of_mul_nonneg_right' {E D : ℝ} (hE : 0 < E) (h : 0 ≤ E * D) : 0 ≤ D :=
  (mul_nonneg_iff_of_pos_left hE).1 h

end Solved.ICG.TwoPb
