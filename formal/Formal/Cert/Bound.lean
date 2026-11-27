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

namespace Solved.Cert.UPoly

/-! ## Interval bounds from coefficientwise sign splitting -/

/-- Coefficientwise positive part `max cᵢ 0`. -/
def posPart (p : UPoly) : UPoly := p.map (max · 0)

/-- Coefficientwise negative part `min cᵢ 0`. -/
def negPart (p : UPoly) : UPoly := p.map (min · 0)

theorem eval_posPart_add_negPart (p : UPoly) (x : ℤ) :
    eval (posPart p) x + eval (negPart p) x = eval p x := by
  induction p with
  | nil => simp [posPart, negPart]
  | cons c cs ih =>
    simp only [posPart, negPart, List.map_cons, eval_cons] at *
    calc max c 0 + x * eval (List.map (max · 0) cs) x + (min c 0 + x * eval (List.map (min · 0) cs) x)
        = (max c 0 + min c 0) + x * (eval (List.map (max · 0) cs) x +
            eval (List.map (min · 0) cs) x) := by ring
      _ = c + x * eval cs x := by rw [max_add_min, ih, add_zero]

theorem eval_posPart_nonneg (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : 0 ≤ eval (posPart p) x := by
  refine eval_nonneg_of_allNonneg ?_ hx
  simp [posPart, allNonneg]

theorem eval_negPart_nonpos (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : eval (negPart p) x ≤ 0 := by
  refine eval_nonpos_of_allNonpos ?_ hx
  simp [negPart, allNonpos]

theorem eval_le_posPart (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : eval p x ≤ eval (posPart p) x := by
  have := eval_posPart_add_negPart p x
  have := eval_negPart_nonpos p hx
  linarith

theorem negPart_le_eval (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : eval (negPart p) x ≤ eval p x := by
  have := eval_posPart_add_negPart p x
  have := eval_posPart_nonneg p hx
  linarith

/-- Coefficientwise maximum, missing coefficients read as `0`. -/
def cmax : UPoly → UPoly → UPoly
  | [], q => posPart q
  | a :: p, [] => posPart (a :: p)
  | a :: p, b :: q => max a b :: cmax p q

theorem eval_le_cmax_left (p q : UPoly) {x : ℤ} (hx : 0 ≤ x) : eval p x ≤ eval (cmax p q) x := by
  induction p generalizing q with
  | nil => exact eval_posPart_nonneg q hx
  | cons a p ih =>
    cases q with
    | nil => exact eval_le_posPart _ hx
    | cons b q =>
      simp only [cmax, eval_cons]
      exact add_le_add (le_max_left a b) (mul_le_mul_of_nonneg_left (ih q) hx)

theorem eval_le_cmax_right (p q : UPoly) {x : ℤ} (hx : 0 ≤ x) : eval q x ≤ eval (cmax p q) x := by
  induction p generalizing q with
  | nil => exact eval_le_posPart q hx
  | cons a p ih =>
    cases q with
    | nil => exact eval_posPart_nonneg _ hx
    | cons b q =>
      simp only [cmax, eval_cons]
      exact add_le_add (le_max_right a b) (mul_le_mul_of_nonneg_left (ih q) hx)

theorem eval_absC_nonneg (p : UPoly) {x : ℤ} (hx : 0 ≤ x) : 0 ≤ eval (absC p) x :=
  (abs_nonneg _).trans (abs_eval_le_absC p hx)

end Solved.Cert.UPoly
