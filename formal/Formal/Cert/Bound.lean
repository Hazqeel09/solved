import Formal.Cert.UPoly

/-!
# Coefficient bounds after a shift

For `x ≥ 0`, `|∑ cₖ xᵏ| ≤ ∑ |cₖ| xᵏ`; combined with `UPoly.shift` this bounds the absolute
value of a polynomial on `[p₀, ∞)` by a polynomial with nonnegative coefficients. Sign
certificates (all shifted coefficients of one sign) give the exact absolute value.
-/

namespace Solved.Cert.UPoly

/-- Coefficientwise absolute value. -/
def absC (p : UPoly) : UPoly := p.map (fun c => |c|)

theorem abs_eval_le_absC (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : |eval p x| ≤ eval (absC p) x := by
  induction p with
  | nil => simp [absC]
  | cons c cs ih =>
    simp only [absC, List.map_cons, eval_cons] at *
    calc |c + x * eval cs x| ≤ |c| + |x * eval cs x| := abs_add_le _ _
      _ = |c| + x * |eval cs x| := by rw [abs_mul, abs_of_nonneg hx]
      _ ≤ |c| + x * eval (List.map (fun c => |c|) cs) x := by gcongr

/-- All coefficients are nonpositive. -/
def allNonpos (p : UPoly) : Bool := p.all (· ≤ 0)

theorem eval_nonpos_of_allNonpos {p : UPoly} (h : allNonpos p = true) {x : ℤ} (hx : 0 ≤ x) :
    eval p x ≤ 0 := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    simp only [allNonpos, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [eval_cons]
    exact add_nonpos h.1 (mul_nonpos_of_nonneg_of_nonpos hx (ih h.2))

/-- Strict positivity certificate: constant term positive, all coefficients nonnegative. -/
def posCert (p : UPoly) : Bool :=
  match p with
  | [] => false
  | c :: cs => decide (0 < c) && allNonneg cs

theorem eval_pos_of_posCert {p : UPoly} (h : posCert p = true) {x : ℤ} (hx : 0 ≤ x) :
    0 < eval p x := by
  cases p with
  | nil => simp [posCert] at h
  | cons c cs =>
    simp only [posCert, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [eval_cons]
    exact add_pos_of_pos_of_nonneg h.1 (mul_nonneg hx (eval_nonneg_of_allNonneg h.2 hx))

/-- All coefficients vanish. -/
def allZero (p : UPoly) : Bool := p.all (· = 0)

theorem eval_eq_zero_of_allZero {p : UPoly} (h : allZero p = true) (x : ℤ) : eval p x = 0 := by
  induction p with
  | nil => simp
  | cons c cs ih =>
    simp only [allZero, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    simp [h.1, ih h.2]

/-- Negation. -/
def neg (p : UPoly) : UPoly := scale (-1) p

@[simp] theorem eval_neg (p : UPoly) (x : ℤ) : eval (neg p) x = -eval p x := by
  simp [neg]

end Solved.Cert.UPoly
