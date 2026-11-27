import Mathlib.Tactic

/-!
# Kernel-computable univariate integer polynomials

Coefficient lists, lowest degree first, with Horner evaluation. Every operation is a
structurally recursive function on lists of integers, so certificate checks built from them
reduce in the kernel (`decide +kernel`) using the kernel's GMP-accelerated integer arithmetic.
Each operation has an evaluation lemma, so a check on coefficients transfers to values.
-/

namespace Solved.Cert

/-- A univariate integer polynomial `∑ cᵢ xⁱ` as `[c₀, c₁, …]`. -/
abbrev UPoly := List ℤ

namespace UPoly

/-- Horner evaluation: `eval (c :: cs) x = c + x * eval cs x`. -/
def eval : UPoly → ℤ → ℤ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

@[simp] theorem eval_nil (x : ℤ) : eval [] x = 0 := rfl

@[simp] theorem eval_cons (c : ℤ) (cs : UPoly) (x : ℤ) :
    eval (c :: cs) x = c + x * eval cs x := rfl

/-- Coefficientwise sum. -/
def add : UPoly → UPoly → UPoly
  | [], q => q
  | p@(_ :: _), [] => p
  | a :: p, b :: q => (a + b) :: add p q

@[simp] theorem eval_add (p q : UPoly) (x : ℤ) : eval (add p q) x = eval p x + eval q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

/-- Multiplication by a constant. -/
def scale (c : ℤ) (p : UPoly) : UPoly := p.map (c * ·)

@[simp] theorem eval_scale (c : ℤ) (p : UPoly) (x : ℤ) : eval (scale c p) x = c * eval p x := by
  induction p with
  | nil => simp [scale]
  | cons a p ih => simp only [scale, List.map_cons, eval_cons] at *; rw [ih]; ring

/-- Polynomial product by distributing over the first factor. -/
def mul : UPoly → UPoly → UPoly
  | [], _ => []
  | a :: p, q => add (scale a q) (0 :: mul p q)

@[simp] theorem eval_mul (p q : UPoly) (x : ℤ) : eval (mul p q) x = eval p x * eval q x := by
  induction p with
  | nil => simp [mul]
  | cons a p ih => simp [mul, ih]; ring

/-- Taylor shift by one: `eval (shift1 p) x = eval p (x + 1)`.
`c + (x+1) Q(x+1) = c + Q(x+1) + x Q(x+1)`. -/
def shift1 : UPoly → UPoly
  | [] => []
  | c :: cs => let s := shift1 cs; add [c] (add s (0 :: s))

@[simp] theorem eval_shift1 (p : UPoly) (x : ℤ) : eval (shift1 p) x = eval p (x + 1) := by
  induction p with
  | nil => simp [shift1]
  | cons c cs ih => simp [shift1, ih]; ring

/-- Shift by a natural number `k`: `eval (shift k p) x = eval p (x + k)`. -/
def shift : ℕ → UPoly → UPoly
  | 0, p => p
  | k + 1, p => shift1 (shift k p)

@[simp] theorem eval_shift (k : ℕ) (p : UPoly) (x : ℤ) :
    eval (shift k p) x = eval p (x + k) := by
  induction k generalizing x with
  | zero => simp [shift]
  | succ k ih => simp [shift, ih]; ring_nf

/-- All coefficients are nonnegative. -/
def allNonneg (p : UPoly) : Bool := p.all (0 ≤ ·)

theorem eval_nonneg_of_allNonneg {p : UPoly} (h : allNonneg p = true) {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ eval p x := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    simp only [allNonneg, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [eval_cons]
    exact add_nonneg h.1 (mul_nonneg hx (ih h.2))

end UPoly
end Solved.Cert
