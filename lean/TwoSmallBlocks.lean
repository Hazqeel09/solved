import Compression

namespace SolvedTwoSmall
open SolvedCompression

theorem strict_iterSq {a b : Nat} (lt : a < b) (g : Nat) : iterSq g a < iterSq g b := by
  induction g with
  | zero => exact lt
  | succ g ih =>
    change iterSq g a * iterSq g a < iterSq g b * iterSq g b
    exact Nat.lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.le_of_lt ih))
      (Nat.mul_lt_mul_of_pos_right ih (by omega))

theorem lift_le {a b : Nat} (g : Nat) : iterSq g a ≤ iterSq g b ↔ a ≤ b := by
  constructor
  · intro h
    by_cases hab : a ≤ b
    · exact hab
    · have strict := strict_iterSq (show b < a by omega) g
      omega
  · intro h
    rcases Nat.eq_or_lt_of_le h with e | lt
    · subst b; exact Nat.le_refl _
    · exact Nat.le_of_lt (strict_iterSq lt g)

theorem proper_sum {x y w : Nat} (xy : x < y) (wx : w ≤ x) :
    x*x+w < y*y := by
  have h := Nat.mul_le_mul (show x+1 ≤ y by omega) (show x+1 ≤ y by omega)
  simp [Nat.mul_add,Nat.add_mul] at h
  omega

-- g = d+k squares. The selected inner operand has had k squares.
theorem lag_crossing (m u d k : Nat) :
    iterSq (d+k) u ≤ iterSq (d+k) m * iterSq k m ↔ iterSq d u ≤ iterSq d m * m := by
  rw [iterSq_add, iterSq_add, ← iterSq_mul, lift_le]

#print axioms proper_sum
#print axioms lag_crossing
end SolvedTwoSmall
