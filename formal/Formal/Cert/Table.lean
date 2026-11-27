import Formal.Cert.Bound

/-!
# Tables of polynomials

A `Table` is a finite family of polynomials indexed by position, positions past the end read as
the zero polynomial. Certificates keep one polynomial per summand of an energy
`∑ₑ |fₑ(x)|`; `bound` and `bound2` turn a table into one polynomial that dominates that sum for
`x ≥ 0`.
-/

namespace Solved.Cert

open Finset

/-- A finite family of polynomials; missing positions are `0`. -/
abbrev Table := List UPoly

namespace Table

/-- Entry `e`, or the zero polynomial past the end. -/
def get : Table → ℕ → UPoly
  | [], _ => []
  | f :: _, 0 => f
  | _ :: t, e + 1 => get t e

@[simp] theorem get_nil (e : ℕ) : get [] e = [] := by cases e <;> rfl
@[simp] theorem get_cons_zero (f : UPoly) (t : Table) : get (f :: t) 0 = f := rfl
@[simp] theorem get_cons_succ (f : UPoly) (t : Table) (e : ℕ) : get (f :: t) (e + 1) = get t e :=
  rfl

theorem get_eq_getElem (t : Table) {e : ℕ} (h : e < t.length) : t.get e = t[e] := by
  induction t generalizing e with
  | nil => simp at h
  | cons f t ih =>
    cases e with
    | zero => rfl
    | succ e => simpa using ih (by simpa using h)

theorem get_map_range (n : ℕ) (f : ℕ → UPoly) {e : ℕ} (h : e < n) :
    get ((List.range n).map f) e = f e := by
  rw [get_eq_getElem _ (by simpa using h)]
  simp

/-- Entrywise sum. -/
def add : Table → Table → Table
  | [], t => t
  | f :: s, [] => f :: s
  | f :: s, g :: t => UPoly.add f g :: add s t

@[simp] theorem eval_get_add (s t : Table) (e : ℕ) (x : ℤ) :
    UPoly.eval ((add s t).get e) x = UPoly.eval (s.get e) x + UPoly.eval (t.get e) x := by
  induction s generalizing t e with
  | nil => simp [add]
  | cons f s ih =>
    cases t with
    | nil => cases e <;> simp [add]
    | cons g t => cases e <;> simp [add, ih]

theorem get_map (φ : UPoly → UPoly) (hφ : φ [] = []) (t : Table) (e : ℕ) :
    get (List.map φ t) e = φ (get t e) := by
  induction t generalizing e with
  | nil => simp [hφ]
  | cons f t ih =>
    cases e with
    | zero => rfl
    | succ e => exact ih e

/-- `∑ₑ absC tₑ`: dominates `∑ₑ |tₑ(x)|` for `x ≥ 0`. -/
def bound : Table → UPoly
  | [] => []
  | f :: t => UPoly.add (UPoly.absC f) (bound t)

theorem eval_bound_nonneg (t : Table) {x : ℤ} (hx : 0 ≤ x) : 0 ≤ UPoly.eval (bound t) x := by
  induction t with
  | nil => simp [bound]
  | cons f t ih => simp only [bound, UPoly.eval_add]; exact add_nonneg (UPoly.eval_absC_nonneg f hx) ih

theorem sum_abs_le_bound (t : Table) {x : ℤ} (hx : 0 ≤ x) (m : ℕ) :
    ∑ e ∈ range m, |UPoly.eval (t.get e) x| ≤ UPoly.eval (bound t) x := by
  induction t generalizing m with
  | nil => simp [bound]
  | cons f t ih =>
    cases m with
    | zero => simpa using eval_bound_nonneg (f :: t) hx
    | succ m =>
      rw [sum_range_succ']
      simp only [get_cons_succ, get_cons_zero, bound, UPoly.eval_add]
      exact add_comm (UPoly.eval (UPoly.absC f) x) _ ▸
        add_le_add (ih m) (UPoly.abs_eval_le_absC f hx)

/-- `∑ₑ cmax (absC sₑ) (absC tₑ)`: dominates `∑ₑ max |sₑ(x)| |tₑ(x)|` for `x ≥ 0`. -/
def bound2 : Table → Table → UPoly
  | [], t => bound t
  | f :: s, [] => bound (f :: s)
  | f :: s, g :: t => UPoly.add (UPoly.cmax (UPoly.absC f) (UPoly.absC g)) (bound2 s t)

theorem eval_bound2_nonneg (s t : Table) {x : ℤ} (hx : 0 ≤ x) :
    0 ≤ UPoly.eval (bound2 s t) x := by
  induction s generalizing t with
  | nil => exact eval_bound_nonneg t hx
  | cons f s ih =>
    cases t with
    | nil => exact eval_bound_nonneg _ hx
    | cons g t =>
      simp only [bound2, UPoly.eval_add]
      exact add_nonneg ((UPoly.eval_absC_nonneg f hx).trans (UPoly.eval_le_cmax_left _ _ hx)) (ih t)

theorem sum_max_le_bound2 (s t : Table) {x : ℤ} (hx : 0 ≤ x) (m : ℕ) :
    ∑ e ∈ range m, max |UPoly.eval (s.get e) x| |UPoly.eval (t.get e) x| ≤
      UPoly.eval (bound2 s t) x := by
  induction s generalizing t m with
  | nil => simpa [bound2] using sum_abs_le_bound t hx m
  | cons f s ih =>
    cases t with
    | nil => simpa [bound2] using sum_abs_le_bound (f :: s) hx m
    | cons g t =>
      cases m with
      | zero => simpa using eval_bound2_nonneg (f :: s) (g :: t) hx
      | succ m =>
        rw [sum_range_succ']
        simp only [get_cons_succ, get_cons_zero, bound2, UPoly.eval_add]
        refine add_comm (UPoly.eval (UPoly.cmax (UPoly.absC f) (UPoly.absC g)) x) _ ▸
          add_le_add (ih t m) (max_le ?_ ?_)
        · exact (UPoly.abs_eval_le_absC f hx).trans (UPoly.eval_le_cmax_left _ _ hx)
        · exact (UPoly.abs_eval_le_absC g hx).trans (UPoly.eval_le_cmax_right _ _ hx)

end Table
end Solved.Cert
