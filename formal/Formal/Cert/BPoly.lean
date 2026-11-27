import Formal.Cert.UPoly

/-!
# Kernel-computable bivariate integer polynomials

`[P₀, P₁, …]` is `∑ᵢ xⁱ Pᵢ(y)` with each `Pᵢ` a `UPoly` in `y`. Every operation is structural
recursion on lists with an evaluation lemma. `compose f c₀ c₁ c₂` substitutes the affine form
`c₀ + c₁ x + c₂ y` into a univariate `f`; certificates use it to rewrite polynomials in two primes
on a region such as `p = p₀ + x`, `q = p₀ + 2 + x + y`, where `x, y ≥ 0` cover the region.
-/

namespace Solved.Cert

open Finset

/-- `∑ᵢ xⁱ Pᵢ(y)`. -/
abbrev BPoly := List UPoly

namespace BPoly

/-- Horner evaluation in `x`. -/
def eval : BPoly → ℤ → ℤ → ℤ
  | [], _, _ => 0
  | Q :: P, x, y => UPoly.eval Q y + x * eval P x y

@[simp] theorem eval_nil (x y : ℤ) : eval [] x y = 0 := rfl
@[simp] theorem eval_cons (Q : UPoly) (P : BPoly) (x y : ℤ) :
    eval (Q :: P) x y = UPoly.eval Q y + x * eval P x y := rfl

/-- Sum. -/
def add : BPoly → BPoly → BPoly
  | [], Q => Q
  | A :: P, [] => A :: P
  | A :: P, B :: Q => UPoly.add A B :: add P Q

@[simp] theorem eval_add (P Q : BPoly) (x y : ℤ) : eval (add P Q) x y = eval P x y + eval Q x y := by
  induction P generalizing Q with
  | nil => simp [add]
  | cons A P ih =>
    cases Q with
    | nil => simp [add]
    | cons B Q => simp [add, ih]; ring

/-- Multiplication by a constant. -/
def scale (c : ℤ) (P : BPoly) : BPoly := P.map (UPoly.scale c)

@[simp] theorem eval_scale (c : ℤ) (P : BPoly) (x y : ℤ) : eval (scale c P) x y = c * eval P x y := by
  induction P with
  | nil => simp [scale]
  | cons A P ih => simp only [scale, List.map_cons, eval_cons, UPoly.eval_scale] at *; rw [ih]; ring

/-- Multiplication by `x`. -/
def mulX (P : BPoly) : BPoly := [] :: P

@[simp] theorem eval_mulX (P : BPoly) (x y : ℤ) : eval (mulX P) x y = x * eval P x y := by
  simp [mulX]

/-- Multiplication by `y`. -/
def mulY (P : BPoly) : BPoly := P.map fun Q => 0 :: Q

@[simp] theorem eval_mulY (P : BPoly) (x y : ℤ) : eval (mulY P) x y = y * eval P x y := by
  induction P with
  | nil => simp [mulY]
  | cons A P ih => simp only [mulY, List.map_cons, eval_cons, UPoly.eval_cons] at *; rw [ih]; ring

/-- Multiplication by `c₀ + c₁ x + c₂ y`. -/
def mulLin (c0 c1 c2 : ℤ) (P : BPoly) : BPoly :=
  add (scale c0 P) (add (scale c1 (mulX P)) (scale c2 (mulY P)))

@[simp] theorem eval_mulLin (c0 c1 c2 : ℤ) (P : BPoly) (x y : ℤ) :
    eval (mulLin c0 c1 c2 P) x y = (c0 + c1 * x + c2 * y) * eval P x y := by
  simp [mulLin]; ring

/-- `f (c₀ + c₁ x + c₂ y)` for a univariate `f`, by Horner's scheme. -/
def compose : UPoly → ℤ → ℤ → ℤ → BPoly
  | [], _, _, _ => []
  | a :: f, c0, c1, c2 => add [[a]] (mulLin c0 c1 c2 (compose f c0 c1 c2))

@[simp] theorem eval_compose (f : UPoly) (c0 c1 c2 x y : ℤ) :
    eval (compose f c0 c1 c2) x y = UPoly.eval f (c0 + c1 * x + c2 * y) := by
  induction f with
  | nil => simp [compose]
  | cons a f ih => simp [compose, ih]

/-- Product, distributing over the first factor. -/
def mul : BPoly → BPoly → BPoly
  | [], _ => []
  | A :: P, Q => add (Q.map (UPoly.mul A)) (mulX (mul P Q))

theorem eval_map_mul (A : UPoly) (Q : BPoly) (x y : ℤ) :
    eval (Q.map (UPoly.mul A)) x y = UPoly.eval A y * eval Q x y := by
  induction Q with
  | nil => simp
  | cons B Q ih => simp only [List.map_cons, eval_cons, UPoly.eval_mul, ih]; ring

@[simp] theorem eval_mul (P Q : BPoly) (x y : ℤ) : eval (mul P Q) x y = eval P x y * eval Q x y := by
  induction P with
  | nil => simp [mul]
  | cons A P ih => simp [mul, eval_map_mul, ih]; ring

/-! ## Coefficients -/

/-- Coefficient of `xⁱ yʲ`. -/
def coeff : BPoly → ℕ → ℕ → ℤ
  | [], _, _ => 0
  | Q :: _, 0, j => UPoly.coeff Q j
  | _ :: P, i + 1, j => coeff P i j

@[simp] theorem coeff_nil (i j : ℕ) : coeff [] i j = 0 := by cases i <;> rfl

/-- With at most `Dx` rows of length at most `Dy`, `P = ∑ᵢ ∑ⱼ coeff P i j xⁱ yʲ`. -/
theorem eval_eq_sum (P : BPoly) {Dx Dy : ℕ} (hx : P.length ≤ Dx) (hy : ∀ Q ∈ P, Q.length ≤ Dy)
    (x y : ℤ) :
    eval P x y = ∑ i ∈ range Dx, ∑ j ∈ range Dy, coeff P i j * (x ^ i * y ^ j) := by
  induction P generalizing Dx with
  | nil => simp
  | cons Q P ih =>
    obtain ⟨Dx, rfl⟩ : ∃ D', Dx = D' + 1 := ⟨Dx - 1, by simp at hx; omega⟩
    rw [eval_cons, sum_range_succ', ih (by simpa using hx) fun R hR => hy R (by simp [hR]),
      mul_sum, UPoly.eval_eq_sum_coeff Q (hy Q (by simp))]
    simp only [coeff, pow_zero, one_mul]
    rw [add_comm]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
    exact sum_congr rfl fun j _ => by ring

end BPoly
end Solved.Cert
