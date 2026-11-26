import Compression
import TwoSmallBlocks

namespace SolvedSubtraction
open SolvedCompression SolvedTwoSmall

-- A strict integer power gap prevents two comparable marked descriptions
-- from representing distinct tower-minus-one endpoints at the same excess.
theorem square_gap {a b : Nat} (positive : 0 < a) (strict : a < b) :
    a*a+1 < b*b := by
  have bound := Nat.mul_le_mul (show a+1 ≤ b by omega) (show a+1 ≤ b by omega)
  simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at bound
  omega

theorem one_run (q : Nat) : iterSq q 1 = 1 := by
  induction q with
  | zero => rfl
  | succ q ih => simp only [iterSq, ih, Nat.mul_one]

theorem tower_minus_one {a : Nat} (large : 2 ≤ a) (q : Nat) :
    iterSq (q+1) (a-1) < iterSq (q+1) a - 1 := by
  have pos : 0 < iterSq q (a-1) := by
    have lower := (lift_le q).mpr (show 1 ≤ a-1 by omega)
    rw [one_run] at lower
    omega
  have strict := strict_iterSq (show a-1 < a by omega) q
  have gap := square_gap pos strict
  simp only [iterSq] at *
  omega

theorem incompatible_endpoints {a newer : Nat} (large : 2 ≤ a) (q : Nat)
    (domination : newer ≤ iterSq (q+1) (a-1))
    (tower_identity : newer = iterSq (q+1) a - 1) : False := by
  have gap := tower_minus_one large q
  omega

#print axioms square_gap
#print axioms tower_minus_one
#print axioms incompatible_endpoints
end SolvedSubtraction
