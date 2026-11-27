import Formal.Cert.Bound
import Formal.ICG.LocalPoly
import Research.ICGGeneralThm5

/-!
# A reflective certificate for `ICGGeneral.L1mat 2 p a b`

For orders `2^a p^b` the reused bridge identifies the graph energy with `L1mat 2 p a b Y`,
where `Y` is the indicator of the divisor set on the exponent box. Every entry of `L1mat` is
an integer polynomial in `p`. `check` verifies, by integer polynomial arithmetic that the kernel
evaluates, that a claimed set of maximisers has one common energy and that every other
nonempty mask has strictly smaller energy for all integers `p ≥ p₀`. `check_sound` turns a
successful check into that statement about `L1mat`.
-/

namespace Solved.ICG

open Solved.Cert Finset

/-- `∑_{i < n} f i` as a polynomial. -/
def sumRange : ℕ → (ℕ → UPoly) → UPoly
  | 0, _ => []
  | n + 1, f => UPoly.add (sumRange n f) (f n)

@[simp] theorem eval_sumRange (n : ℕ) (f : ℕ → UPoly) (x : ℤ) :
    UPoly.eval (sumRange n f) x = ∑ i ∈ range n, UPoly.eval (f i) x := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, sum_range_succ]

/-- Bit `k` of a mask (missing bits are `false`). -/
def bit (L : List Bool) (k : ℕ) : Bool := L.getD k false

/-- The indicator on the exponent box `[0,a] × [0,b]`, cell `(i,l)` at index `i(b+1)+l`. -/
def ind (b : ℕ) (L : List Bool) (i l : ℕ) : ℝ := if bit L (i * (b + 1) + l) then 1 else 0

/-- Entry `(u,v)` of `T_a(2) Y T_b(p)ᵀ` as a polynomial in `p`. -/
def entryP (a b : ℕ) (L : List Bool) (u v : ℕ) : UPoly :=
  sumRange (a + 1) fun i => sumRange (b + 1) fun l =>
    if bit L (i * (b + 1) + l) then UPoly.scale (UPoly.eval (tentP a u i) 2) (tentP b v l)
    else []

theorem eval_entryP (a b : ℕ) (L : List Bool) (u v : ℕ) (p : ℤ) :
    ((UPoly.eval (entryP a b L u v) p : ℤ) : ℝ) =
      ICGGeneral.Mentry 2 (p : ℝ) a b (ind b L) u v := by
  unfold entryP ICGGeneral.Mentry ind
  simp only [eval_sumRange, Int.cast_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
  split_ifs with h
  · simp only [UPoly.eval_scale, Int.cast_mul, eval_tentP, Int.cast_ofNat]
    ring
  · simp

theorem L1mat_eq (a b : ℕ) (L : List Bool) (p : ℤ) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) =
      ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        |((UPoly.eval (entryP a b L u v) p : ℤ) : ℝ)| := by
  unfold ICGGeneral.L1mat
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  rw [eval_entryP]

/-! ## The checker -/

/-- Shifted entry `(u,v)` of a mask: a polynomial in `x = p - p₀`. -/
def sentry (a b p0 : ℕ) (L : List Bool) (u v : ℕ) : UPoly := UPoly.shift p0 (entryP a b L u v)

/-- Upper bound for the energy of any mask on `p ≥ p₀`. -/
def upperE (a b p0 : ℕ) (L : List Bool) : UPoly :=
  sumRange (a + 1) fun u => sumRange (b + 1) fun v => UPoly.absC (sentry a b p0 L u v)

/-- Every shifted entry has coefficients of one sign. -/
def signsOK (a b p0 : ℕ) (L : List Bool) : Bool :=
  (List.range (a + 1)).all fun u => (List.range (b + 1)).all fun v =>
    UPoly.allNonneg (sentry a b p0 L u v) || UPoly.allNonpos (sentry a b p0 L u v)

/-- The shifted polynomial with constant sign, made nonnegative. -/
def signed (f : UPoly) : UPoly := if UPoly.allNonneg f then f else UPoly.neg f

/-- Exact energy of a mask whose entries have certified signs. -/
def exactE (a b p0 : ℕ) (L : List Bool) : UPoly :=
  sumRange (a + 1) fun u => sumRange (b + 1) fun v => signed (sentry a b p0 L u v)

/-- All Boolean lists of length `n`. -/
def allMasks : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allMasks n).flatMap fun L => [false :: L, true :: L]

/-- A mask for a nonempty set of proper divisors: some bit set, top cell `(a,b)` unset. -/
def valid (a b : ℕ) (L : List Bool) : Bool := L.any id && !bit L (a * (b + 1) + b)

/-- The certificate: `star` and `others` share one exact energy, and every other valid mask of
the box has strictly smaller energy, for all `p ≥ p₀`. -/
def check (a b p0 : ℕ) (star : List Bool) (others : List (List Bool)) : Bool :=
  signsOK a b p0 star &&
  others.all (fun L => signsOK a b p0 L &&
    UPoly.allZero (UPoly.add (exactE a b p0 L) (UPoly.neg (exactE a b p0 star)))) &&
  (allMasks ((a + 1) * (b + 1))).all fun L =>
    !valid a b L || L == star || others.contains L ||
      UPoly.posCert (UPoly.add (exactE a b p0 star) (UPoly.neg (upperE a b p0 L)))

end Solved.ICG
