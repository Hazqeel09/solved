import Compression
import TwoSmallBlocks
import FiniteControls
import NonsquareBound
import ControlInflation

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


-- A checked base excludes every strict coordinate extension satisfying the
-- marked-expression domination bound, at the same written-length excess.
theorem exclusion_by_growth {base candidate n : Nat} (q : Nat)
    (large : 2 ≤ iterSq n 2)
    (base_bound : base ≤ iterSq n 2 - 1)
    (domination : candidate ≤ iterSq (q+1) base) :
    candidate < iterSq (n+(q+1)) 2 - 1 := by
  have propagated := (lift_le (q+1)).mpr base_bound
  have strict := tower_minus_one large q
  rw [iterSq_add]
  exact Nat.lt_of_le_of_lt (Nat.le_trans domination propagated) strict

-- A finite collection of controls cannot represent infinitely many distinct
-- tower-minus-one endpoints at one of finitely many fixed length excesses.
-- The numerical domination hypothesis must be justified by the encoding.
theorem finite_descriptions_obstruction
    (index label : Nat → Nat) (parameters : Nat → Nat → Nat)
    (labelBound dimension : Nat)
    (labels_bounded : ∀ i, label i ≤ labelBound)
    (indices_rise : ∀ i j, i < j → index i < index j)
    (domination : ∀ i j, i < j → label i = label j →
      (∀ k, k < dimension → parameters i k ≤ parameters j k) →
      iterSq (index j) 2 - 1 ≤ iterSq (index j-index i) (iterSq (index i) 2 - 1)) :
    False := by
  let packed := fun i k => if k=0 then label i
    else if k=1 then labelBound-label i else parameters i (k-2)
  obtain ⟨g, rises, ordered⟩ := SolvedControls.thin packed (dimension+2)
  let i := g 0
  let j := g 1
  have ij : i < j := rises 0 1 (by omega)
  have first : label i ≤ label j := by
    have h := ordered 0 (by omega) 0 1 (by omega)
    simpa only [packed, if_pos rfl] using h
  have second : labelBound-label i ≤ labelBound-label j := by
    have h := ordered 1 (by omega) 0 1 (by omega)
    simpa only [packed, Nat.one_ne_zero, if_false, if_pos rfl] using h
  have same : label i=label j := by
    have hi := labels_bounded i
    have hj := labels_bounded j
    omega
  have params : ∀ k, k < dimension → parameters i k ≤ parameters j k := by
    intro k hk
    have h := ordered (k+2) (by omega) 0 1 (by omega)
    have nz : k+2 ≠ 0 := by omega
    have no : k+2 ≠ 1 := by omega
    simpa only [packed, if_neg nz, if_neg no, Nat.add_sub_cancel] using h
  have bound := domination i j ij same params
  have increase := indices_rise i j ij
  have positive : 0 < index j-index i := by omega
  have gap : index j-index i = (index j-index i-1)+1 := by omega
  have large : 2 ≤ iterSq (index i) 2 := by
    have h := strict_iterSq (show 1 < 2 by omega) (index i)
    rw [one_run] at h
    omega
  have tower : iterSq (index j) 2 - 1 =
      iterSq ((index j-index i-1)+1) (iterSq (index i) 2) - 1 := by
    rw [← gap, ← iterSq_add]
    have eq : index i+(index j-index i)=index j := by omega
    rw [eq]
  rw [gap] at bound
  exact incompatible_endpoints large (index j-index i-1) bound tower

-- Comparable square-run programs with the same cost excess cannot reach
-- two different members of the tower-minus-one family.
theorem mersenne_program_antichain
    (old new : List SolvedMarked.Instr) (initial : SolvedMarked.Hist)
    (n m excess : Nat) (increasing : n < m)
    (same : SolvedInflation.erase old = SolvedInflation.erase new)
    (parameters : SolvedInflation.Below (SolvedInflation.parameters old)
      (SolvedInflation.parameters new))
    (old_cost : SolvedInflation.cost old = n+excess)
    (new_cost : SolvedInflation.cost new = m+excess)
    (old_value : SolvedMarked.eval old initial 0 = 2^(2^n)-1)
    (new_value : SolvedMarked.eval new initial 0 = 2^(2^m)-1) : False := by
  have domination := SolvedInflation.comparable_domination same parameters initial
  have difference : SolvedInflation.cost new-SolvedInflation.cost old=m-n := by omega
  have gap : m-n=(m-n-1)+1 := by omega
  rw [difference,old_value,new_value,SolvedGrowth.tower_as_squares n,
    SolvedGrowth.tower_as_squares m,gap] at domination
  have large : 2 ≤ iterSq n 2 := by
    rw [← SolvedGrowth.tower_as_squares]
    exact SolvedGrowth.tower_large n
  have identity : iterSq m 2-1=iterSq ((m-n-1)+1) (iterSq n 2)-1 := by
    rw [← iterSq_add]
    have indices : n+((m-n-1)+1)=m := by omega
    rw [indices]
  exact incompatible_endpoints large (m-n-1) domination identity

#print axioms square_gap
#print axioms tower_minus_one
#print axioms incompatible_endpoints
end SolvedSubtraction
