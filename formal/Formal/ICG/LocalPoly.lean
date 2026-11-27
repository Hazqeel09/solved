import Formal.Cert.UPoly
import Research.ICGGeneralPath

/-!
# Local Ramanujan factors as integer polynomials

Computable `UPoly` versions of `ICGGeneral.phiX`, `ICGGeneral.ramX` and `ICGGeneral.Tent`
(H. Dong, ai4math-results), with lemmas identifying their values at an integer point with the
real-valued definitions. They let a certificate about `ICGGeneral.L1mat` be checked by
integer polynomial arithmetic in the kernel.
-/

namespace Solved.ICG

open Solved.Cert

/-- `xᵏ · p` as a coefficient list. -/
def monoMul (k : ℕ) (p : UPoly) : UPoly := List.replicate k 0 ++ p

@[simp] theorem eval_monoMul (k : ℕ) (p : UPoly) (x : ℤ) :
    UPoly.eval (monoMul k p) x = x ^ k * UPoly.eval p x := by
  induction k with
  | zero => simp [monoMul]
  | succ k ih =>
    simp only [monoMul, List.replicate_succ, List.cons_append, UPoly.eval_cons] at *
    rw [ih]; ring

/-- `φ(x^e)`: `1` for `e = 0`, else `x^(e-1) (x - 1)`. -/
def phiP (e : ℕ) : UPoly := if e = 0 then [1] else monoMul (e - 1) [-1, 1]

/-- The prime-power Ramanujan sum `c_{x^k}(x^u)` as a polynomial in `x`. -/
def ramP (k u : ℕ) : UPoly :=
  if k = 0 then [1] else if k ≤ u then phiP k else if k = u + 1 then monoMul u [-1] else []

/-- `Tent x m u j = φ(x^{m-u}) c_{x^{m-j}}(x^u)` as a polynomial in `x`. -/
def tentP (m u j : ℕ) : UPoly := UPoly.mul (phiP (m - u)) (ramP (m - j) u)

theorem eval_phiP (e : ℕ) (x : ℤ) :
    ((UPoly.eval (phiP e) x : ℤ) : ℝ) = ICGGeneral.phiX (x : ℝ) e := by
  unfold phiP ICGGeneral.phiX
  split_ifs with h
  · simp
  · simp only [eval_monoMul, UPoly.eval_cons, UPoly.eval_nil]
    push_cast
    ring

theorem eval_ramP (k u : ℕ) (x : ℤ) :
    ((UPoly.eval (ramP k u) x : ℤ) : ℝ) = ICGGeneral.ramX (x : ℝ) k u := by
  unfold ramP ICGGeneral.ramX
  split_ifs with h0 h1 h2
  · simp
  · exact eval_phiP k x
  · simp only [eval_monoMul, UPoly.eval_cons, UPoly.eval_nil]
    push_cast
    ring
  · simp

theorem eval_tentP (m u j : ℕ) (x : ℤ) :
    ((UPoly.eval (tentP m u j) x : ℤ) : ℝ) = ICGGeneral.Tent (x : ℝ) m u j := by
  unfold tentP ICGGeneral.Tent
  rw [UPoly.eval_mul]; push_cast
  rw [eval_phiP, eval_ramP]

end Solved.ICG
