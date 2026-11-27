import Formal.Cert.BPoly
import Formal.ICG.Box
import Formal.ICG.LocalPoly
import Formal.Cert.Sums

/-!
# Cell contributions of a multi-prime order on a region

An order `∏ᵢ rᵢ^{aᵢ}` has fixed primes (`slot i = 0`, value `fixedP i`) and up to two symbolic
primes (`slot i = 1` or `2`). On a region, symbolic prime `j` is the affine form
`σⱼ = c₀ + c₁ x + c₂ y` in coordinates `x, y ≥ 0`, for example `p = p₀ + x`,
`q = p₀ + 2 + x + y` for `p < q`. The contribution of cell `c` to the class `u` in the spectral
bridge is `∏ᵢ Tent rᵢ aᵢ uᵢ cᵢ`; `cellB` is that product as a bivariate polynomial in `x, y`
(`eval_cellB`), and `flat` lists its coefficients for the packed certificate.
-/

namespace Solved.ICG.Multi

open Solved.Cert Finset

variable {k : ℕ}

/-- An affine form `c₀ + c₁ x + c₂ y`. -/
structure Affine where
  c0 : ℤ
  c1 : ℤ
  c2 : ℤ

/-- Its value at `(x, y)`. -/
def Affine.val (σ : Affine) (x y : ℤ) : ℤ := σ.c0 + σ.c1 * x + σ.c2 * y

/-- The data of an order on a region: exponents, the kind of each prime, the fixed primes, and
the affine forms of the two symbolic primes. -/
structure Shape (k : ℕ) where
  a : Fin k → ℕ
  slot : Fin k → ℕ
  fixedP : Fin k → ℕ
  σ1 : Affine
  σ2 : Affine

/-- The value of prime `i` at a point of the region. -/
def Shape.prime (s : Shape k) (x y : ℤ) (i : Fin k) : ℤ :=
  if s.slot i = 1 then s.σ1.val x y else if s.slot i = 2 then s.σ2.val x y else s.fixedP i

/-- The factor of prime `i` in the contribution of cell `c` to class `u`. -/
def Shape.factor (s : Shape k) (u c : Fin k → ℕ) (i : Fin k) : BPoly :=
  let t := tentP (s.a i) (u i) (c i)
  if s.slot i = 1 then BPoly.compose t s.σ1.c0 s.σ1.c1 s.σ1.c2
  else if s.slot i = 2 then BPoly.compose t s.σ2.c0 s.σ2.c1 s.σ2.c2
  else [[UPoly.eval t (s.fixedP i)]]

theorem Shape.eval_factor (s : Shape k) (u c : Fin k → ℕ) (i : Fin k) (x y : ℤ) :
    BPoly.eval (s.factor u c i) x y = UPoly.eval (tentP (s.a i) (u i) (c i)) (s.prime x y i) := by
  unfold Shape.factor Shape.prime Affine.val
  split_ifs <;> simp

/-- The product of a list of bivariate polynomials. -/
def prodB : List BPoly → BPoly
  | [] => [[1]]
  | P :: Ps => BPoly.mul P (prodB Ps)

theorem eval_prodB (Ps : List BPoly) (x y : ℤ) :
    BPoly.eval (prodB Ps) x y = (Ps.map fun P => BPoly.eval P x y).prod := by
  induction Ps with
  | nil => simp [prodB]
  | cons P Ps ih => simp [prodB, ih]

/-- The contribution of cell `c` to class `u`, as a polynomial in the region coordinates. -/
def Shape.cellB (s : Shape k) (u c : Fin k → ℕ) : BPoly :=
  prodB ((List.finRange k).map (s.factor u c))

theorem Shape.eval_cellB (s : Shape k) (u c : Fin k → ℕ) (x y : ℤ) :
    BPoly.eval (s.cellB u c) x y =
      ∏ i, UPoly.eval (tentP (s.a i) (u i) (c i)) (s.prime x y i) := by
  rw [Shape.cellB, eval_prodB, List.map_map, Fin.prod_univ_def]
  congr 1
  exact List.map_congr_left fun i _ => s.eval_factor u c i x y

/-- The same product with the real `Tent` of the spectral bridge. -/
theorem Shape.cast_eval_cellB (s : Shape k) (u c : Fin k → ℕ) (x y : ℤ) :
    ((BPoly.eval (s.cellB u c) x y : ℤ) : ℝ) =
      ∏ i, ICGGeneral.Tent ((s.prime x y i : ℤ) : ℝ) (s.a i) (u i) (c i) := by
  rw [s.eval_cellB, Int.cast_prod]
  exact prod_congr rfl fun i _ => eval_tentP _ _ _ _

/-! ## Flat coefficient lists -/

/-- The coefficients `coeff P i j` at `i * Dy + j`, for `i < Dx`, `j < Dy`. -/
def flat (Dx Dy : ℕ) (P : BPoly) : UPoly :=
  (List.range (Dx * Dy)).map fun d => BPoly.coeff P (d / Dy) (d % Dy)

theorem length_flat (Dx Dy : ℕ) (P : BPoly) : (flat Dx Dy P).length = Dx * Dy := by
  simp [flat]

theorem coeff_flat (Dx Dy : ℕ) (P : BPoly) {d : ℕ} (hd : d < Dx * Dy) :
    UPoly.coeff (flat Dx Dy P) d = BPoly.coeff P (d / Dy) (d % Dy) := by
  have key : ∀ (l : UPoly) {d : ℕ} (hd : d < l.length), UPoly.coeff l d = l[d] := by
    intro l
    induction l with
    | nil => intro d hd; simp at hd
    | cons c l ih =>
      intro d hd
      cases d with
      | zero => rfl
      | succ d => simpa using ih (by simpa using hd)
  rw [key _ (by rw [length_flat]; exact hd)]
  simp [flat]

/-- Monomial values `xⁱ yʲ` at `i * Dy + j`. -/
def monos (Dy : ℕ) (x y : ℤ) (d : ℕ) : ℤ := x ^ (d / Dy) * y ^ (d % Dy)

/-- With at most `Dx` rows of length at most `Dy`, the flat coefficients against the monomial
values give the polynomial's value. -/
theorem sum_flat (Dx Dy : ℕ) (P : BPoly) (hx : P.length ≤ Dx) (hy : ∀ Q ∈ P, Q.length ≤ Dy)
    (x y : ℤ) :
    ∑ d ∈ range (Dx * Dy), UPoly.coeff (flat Dx Dy P) d * monos Dy x y d = BPoly.eval P x y := by
  rw [BPoly.eval_eq_sum P hx hy, sum_range_mul_flat]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  have hd : i * Dy + j < Dx * Dy := by
    have := mem_range.1 ‹i ∈ range Dx›
    nlinarith
  rw [coeff_flat Dx Dy P hd, monos, flat_div i hj', flat_mod i hj']

theorem monos_zero (Dy : ℕ) (x y : ℤ) : monos Dy x y 0 = 1 := by simp [monos]

theorem monos_nonneg (Dy : ℕ) {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (d : ℕ) :
    0 ≤ monos Dy x y d := mul_nonneg (pow_nonneg hx _) (pow_nonneg hy _)

end Solved.ICG.Multi
