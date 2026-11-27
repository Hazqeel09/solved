import Formal.ICG.MultiBridge

/-!
# Mixed-radix codes for the exponent box

The exponent vectors `x ≤ a` of a `k`-prime order are numbered `0, …, N-1`, `N = ∏ (aᵢ + 1)`, by
`enc a x = ∑ᵢ xᵢ ∏_{j<i} (aⱼ + 1)` (coordinate 0 least significant), with digits
`dec a e i = ⌊e / ∏_{j<i} (aⱼ + 1)⌋ mod (aᵢ + 1)`. These are Mathlib's `finPiFinEquiv` and its
inverse, so the inverse laws come from that equivalence. The top vector `a` (the order itself)
has the last code `N - 1`.
-/

namespace Solved.ICG.Multi

open Finset

variable {k : ℕ}

/-- The radix `aᵢ + 1` of coordinate `i`. -/
def rad (a : Fin k → ℕ) (i : Fin k) : ℕ := a i + 1

/-- The number of exponent vectors, `∏ (aᵢ + 1)`. -/
def size (a : Fin k → ℕ) : ℕ := ∏ i, rad a i

/-- The place value of coordinate `i`, `∏_{j<i} (aⱼ + 1)`. -/
def stride (a : Fin k → ℕ) (i : Fin k) : ℕ := ∏ j : Fin i, rad a (Fin.castLE i.is_lt.le j)

/-- The code of an exponent vector. -/
def enc (a x : Fin k → ℕ) : ℕ := ∑ i, x i * stride a i

/-- Digit `i` of a code. -/
def dec (a : Fin k → ℕ) (e : ℕ) (i : Fin k) : ℕ := e / stride a i % rad a i

theorem size_pos (a : Fin k → ℕ) : 0 < size a := prod_pos fun i _ => Nat.succ_pos (a i)

theorem dec_mem_box (a : Fin k → ℕ) (e : ℕ) : dec a e ∈ box a :=
  mem_box.2 fun i => Nat.lt_succ_iff.1 (Nat.mod_lt _ (Nat.succ_pos (a i)))

/-- The element of `∀ i, Fin (aᵢ + 1)` of a vector in the box. -/
def toPi {a x : Fin k → ℕ} (hx : x ∈ box a) : ∀ i, Fin (rad a i) :=
  fun i => ⟨x i, Nat.lt_succ_of_le (mem_box.1 hx i)⟩

theorem enc_eq (a : Fin k → ℕ) {x : Fin k → ℕ} (hx : x ∈ box a) :
    ((finPiFinEquiv (toPi hx) : Fin (size a)) : ℕ) = enc a x := by
  rw [finPiFinEquiv_apply]; rfl

theorem dec_eq (a : Fin k → ℕ) {e : ℕ} (he : e < size a) (i : Fin k) :
    ((finPiFinEquiv.symm (⟨e, he⟩ : Fin (size a)) : ∀ i, Fin (rad a i)) i : ℕ) = dec a e i :=
  rfl

theorem enc_lt (a : Fin k → ℕ) {x : Fin k → ℕ} (hx : x ∈ box a) : enc a x < size a := by
  rw [← enc_eq a hx]; exact Fin.is_lt _

theorem dec_enc (a : Fin k → ℕ) {x : Fin k → ℕ} (hx : x ∈ box a) : dec a (enc a x) = x := by
  funext i
  have h2 : finPiFinEquiv (toPi hx) = (⟨enc a x, enc_lt a hx⟩ : Fin (size a)) :=
    Fin.ext (enc_eq a hx)
  have h1 := finPiFinEquiv.symm_apply_apply (toPi hx)
  rw [h2] at h1
  rw [← dec_eq a (enc_lt a hx) i, h1]
  rfl

theorem enc_dec (a : Fin k → ℕ) {e : ℕ} (he : e < size a) : enc a (dec a e) = e := by
  have hg : toPi (dec_mem_box a e) = finPiFinEquiv.symm (⟨e, he⟩ : Fin (size a)) := by
    funext i; exact Fin.ext (dec_eq a he i).symm
  rw [← enc_eq a (dec_mem_box a e), hg]
  exact congrArg Fin.val (finPiFinEquiv.apply_symm_apply _)

theorem enc_inj (a : Fin k → ℕ) {x y : Fin k → ℕ} (hx : x ∈ box a) (hy : y ∈ box a)
    (h : enc a x = enc a y) : x = y := by
  rw [← dec_enc a hx, h, dec_enc a hy]

/-- Sums over the box are sums over codes. -/
theorem sum_box {M : Type*} [AddCommMonoid M] (a : Fin k → ℕ) (F : (Fin k → ℕ) → M) :
    ∑ x ∈ box a, F x = ∑ e ∈ range (size a), F (dec a e) := by
  refine sum_nbij' (enc a) (dec a) (fun x hx => mem_range.2 (enc_lt a hx))
    (fun e _ => dec_mem_box a e) (fun x hx => dec_enc a hx)
    (fun e he => enc_dec a (mem_range.1 he)) fun x hx => ?_
  rw [dec_enc a hx]

/-- The top vector has the last code. -/
theorem enc_top (a : Fin k → ℕ) : enc a a = size a - 1 := by
  have hlt := enc_lt a (mem_box.2 fun i => le_rfl)
  -- every code is at most `enc a a`
  have hmax : ∀ e < size a, e ≤ enc a a := by
    intro e he
    rw [← enc_dec a he]
    exact sum_le_sum fun i _ => Nat.mul_le_mul_right _ (mem_box.1 (dec_mem_box a e) i)
  have := hmax (size a - 1) (Nat.sub_lt (size_pos a) Nat.one_pos)
  omega

theorem dec_top (a : Fin k → ℕ) : dec a (size a - 1) = a := by
  rw [← enc_top, dec_enc a (mem_box.2 fun i => le_rfl)]

end Solved.ICG.Multi
