import Mathlib.Tactic

/-! # Flat indices: `k = i * B + l` -/

namespace Solved.Cert

open Finset

theorem sum_range_mul_flat {M : Type*} [AddCommMonoid M] (A B : ℕ) (f : ℕ → M) :
    ∑ k ∈ range (A * B), f k = ∑ i ∈ range A, ∑ l ∈ range B, f (i * B + l) := by
  induction A with
  | zero => simp
  | succ A ih => rw [add_one_mul, sum_range_add, ih, sum_range_succ]

theorem flat_div {B : ℕ} (i : ℕ) {l : ℕ} (hl : l < B) : (i * B + l) / B = i := by
  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hl, Nat.add_zero]

theorem flat_mod {B : ℕ} (i : ℕ) {l : ℕ} (hl : l < B) : (i * B + l) % B = l := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hl]

/-- One column of a nonnegative `A × B` array is at most the whole sum. -/
theorem col_le_total {A B : ℕ} {g : ℕ → ℤ} (hg : ∀ k < A * B, 0 ≤ g k) {l : ℕ} (hl : l < B) :
    ∑ i ∈ range A, g (i * B + l) ≤ ∑ k ∈ range (A * B), g k := by
  rw [sum_range_mul_flat]
  refine sum_le_sum fun i hi => ?_
  refine single_le_sum (f := fun l => g (i * B + l)) (fun l' hl' => hg _ ?_) (mem_range.2 hl)
  have := mem_range.1 hi
  have := mem_range.1 hl'
  nlinarith

end Solved.Cert
