import DiagonalProfiles
import SubtractionGap

namespace SolvedIdeal
open SolvedMarked SolvedInflation

-- These boxes retain arbitrary positive lower bounds on finite coordinates.
-- Operation addresses are fixed; programs use the established marked machine.
inductive Constraint
  | add (a b : Nat)
  | mul (a b : Nat)
  | bounded (a lo hi : Nat)
  | unbounded (a lo : Nat)
  deriving Repr

def anchor : Constraint → SolvedProfiles.Block
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .bounded a _ hi => .fixed a hi
  | .unbounded a lo => .free a lo

def diagonal (box : List Constraint) (t : Nat) : List Instr :=
  (box.map anchor).map (SolvedProfiles.concrete t)

def Nonempty : List Constraint → Prop
  | [] => True
  | .bounded _ lo hi::tail => 0 < lo ∧ lo ≤ hi ∧ Nonempty tail
  | .unbounded _ lo::tail => 0 < lo ∧ Nonempty tail
  | _::tail => Nonempty tail

inductive Inside : List Constraint → List Instr → Prop
  | nil : Inside [] []
  | add {box code} (a b : Nat) (tail : Inside box code) :
      Inside (.add a b::box) (.add a b::code)
  | mul {box code} (a b : Nat) (tail : Inside box code) :
      Inside (.mul a b::box) (.mul a b::code)
  | bounded {box code} (a lo hi k : Nat) (lower : lo ≤ k) (upper : k ≤ hi)
      (tail : Inside box code) :
      Inside (.bounded a lo hi::box) (.sqRun a k::code)
  | unbounded {box code} (a lo k : Nat) (lower : lo ≤ k) (tail : Inside box code) :
      Inside (.unbounded a lo::box) (.sqRun a k::code)

def height : List Instr → Nat
  | [] => 0
  | .sqRun _ k::tail => max k (height tail)
  | _::tail => height tail

theorem diagonal_inside (box : List Constraint) (t : Nat) (valid : Nonempty box) :
    Inside box (diagonal box t) := by
  induction box with
  | nil => exact Inside.nil
  | cons c tail ih =>
    cases c with
    | add a b => exact Inside.add a b (ih valid)
    | mul a b => exact Inside.mul a b (ih valid)
    | bounded a lo hi => exact Inside.bounded a lo hi hi valid.2.1 (Nat.le_refl _) (ih valid.2.2)
    | unbounded a lo => exact Inside.unbounded a lo (lo+t) (by omega) (ih valid.2)

theorem inside_erasure {box : List Constraint} {code : List Instr}
    (inside : Inside box code) (t : Nat) :
    erase code = erase (diagonal box t) := by
  induction inside with
  | nil => rfl
  | add a b _ ih => exact congrArg (List.cons (.add a b)) ih
  | mul a b _ ih => exact congrArg (List.cons (.mul a b)) ih
  | bounded a _lo _hi _k _lower _upper _ ih => exact congrArg (List.cons (.sq a)) ih
  | unbounded a _lo _k _lower _ ih => exact congrArg (List.cons (.sq a)) ih

theorem inside_below {box : List Constraint} {code : List Instr}
    (inside : Inside box code) (t : Nat) (large : height code ≤ t) :
    Below (parameters code) (parameters (diagonal box t)) := by
  induction inside with
  | nil => exact Below.nil
  | add a b _ ih => exact Below.cons (Nat.le_refl _) (ih large)
  | mul a b _ ih => exact Below.cons (Nat.le_refl _) (ih large)
  | bounded a lo hi k _lower upper _tail ih =>
    have tailBound : height _ ≤ t := Nat.le_trans (Nat.le_max_right k _) large
    exact Below.cons upper (ih tailBound)
  | unbounded a lo k _lower _tail ih =>
    have own : k ≤ t := Nat.le_trans (Nat.le_max_left _ _) large
    have tailBound : height _ ≤ t := Nat.le_trans (Nat.le_max_right k _) large
    exact Below.cons (show k ≤ lo+t by omega) (ih tailBound)

def Hits (code : List Instr) (excess : Nat) : Prop :=
  excess ≤ cost code ∧ eval code (fun _ => 1) 0 ≤ 2^(2^(cost code-excess))-1

def Meets (box : List Constraint) (excess : Nat) : Prop :=
  ∃ code, Inside box code ∧ Hits code excess

theorem hits_upward {old new : List Instr} (same : erase old = erase new)
    (ordered : Below (parameters old) (parameters new)) {excess : Nat}
    (hit : Hits old excess) : Hits new excess := by
  obtain ⟨extra, inflated⟩ := comparable_inflation same ordered
  have costs := inflation_cost inflated
  have domination := inflation_domination inflated (fun _ => 1)
  have difference : cost new-cost old=extra := by omega
  rw [difference, ← runs_agree, SolvedProfiles.squares_power] at domination
  have large := SolvedGrowth.tower_large (cost old-excess)
  have gap : 2^(2^(cost old-excess))-1 < 2^(2^(cost old-excess)) := by omega
  have powers := SolvedEffective.positive_power_strict gap (2^extra-1)
  have positive := Nat.two_pow_pos extra
  have pred : 2^extra-1+1=2^extra := by omega
  rw [pred] at powers
  have compare := Nat.pow_le_pow_of_le_left hit.2 (2^extra)
  have strict := Nat.lt_of_le_of_lt (Nat.le_trans domination compare) powers
  have target : (2^(2^(cost old-excess)))^(2^extra) = 2^(2^(cost new-excess)) := by
    rw [← Nat.pow_mul, ← Nat.pow_add]
    have index : cost old-excess+extra=cost new-excess := by have := hit.1; omega
    rw [index]
  rw [target] at strict
  exact ⟨by have := hit.1; omega, by omega⟩

theorem meets_iff_diagonal (box : List Constraint) (excess : Nat)
    (valid : Nonempty box) :
    Meets box excess ↔ ∃ t, Hits (diagonal box t) excess := by
  constructor
  · intro ⟨code,inside,hit⟩
    exact ⟨height code, hits_upward (inside_erasure inside _) (inside_below inside _ (Nat.le_refl _)) hit⟩
  · intro ⟨t,hit⟩
    exact ⟨diagonal box t, diagonal_inside box t valid, hit⟩

theorem zero_free_diagonal (code : List SolvedProfiles.Block)
    (zero : SolvedProfiles.freeCount code=0) (t : Nat) :
    code.map (SolvedProfiles.concrete t) = code.map (SolvedProfiles.concrete 0) := by
  induction code with
  | nil => rfl
  | cons block tail ih =>
    cases block <;>
      simp only [SolvedProfiles.freeCount, SolvedProfiles.freeBlock, Nat.zero_add] at zero
    · exact congrArg (List.cons (.add _ _)) (ih zero)
    · exact congrArg (List.cons (.mul _ _)) (ih zero)
    · exact congrArg (List.cons (.sqRun _ _)) (ih zero)
    · omega

theorem diagonal_index (box : List Constraint) (excess t : Nat)
    (valid : excess ≤ cost (diagonal box 0)) :
    excess ≤ cost (diagonal box t) ∧
    cost (diagonal box t)-excess =
      cost (diagonal box 0)-excess + SolvedProfiles.freeCount (box.map anchor)*t := by
  have costs := SolvedProfiles.concrete_cost (box.map anchor) t
  change cost (diagonal box t) = cost (diagonal box 0) +
    SolvedProfiles.freeCount (box.map anchor)*t at costs
  have nonnegative := Nat.zero_le (SolvedProfiles.freeCount (box.map anchor)*t)
  omega

theorem hits_diagonal_iff (box : List Constraint) (excess t : Nat)
    (valid : excess ≤ cost (diagonal box 0)) :
    Hits (diagonal box t) excess ↔
    SolvedProfiles.endpoint (box.map anchor) t ≤
      (2^(2^(cost (diagonal box 0)-excess)))^
        ((2^t)^(SolvedProfiles.freeCount (box.map anchor)))-1 := by
  have indices := diagonal_index box excess t valid
  rw [SolvedProfiles.diagonal_target, ← indices.2]
  constructor
  · intro hit; exact hit.2
  · intro hit; exact ⟨indices.1,hit⟩

-- No supplied profile bounds or unproved ideal oracle are hypotheses here.
theorem ideal_criterion (box : List Constraint) (excess : Nat)
    (valid : Nonempty box) (indexValid : excess ≤ cost (diagonal box 0)) :
    Meets box excess ↔
      if SolvedProfiles.freeCount (box.map anchor)=0 then Hits (diagonal box 0) excess
      else SolvedProfiles.leading (box.map anchor) < 2^(2^(cost (diagonal box 0)-excess)) := by
  rw [meets_iff_diagonal box excess valid]
  split
  · rename_i zero
    constructor
    · intro ⟨t,hit⟩
      have same := zero_free_diagonal (box.map anchor) zero t
      change diagonal box t = diagonal box 0 at same
      rw [same] at hit
      exact hit
    · intro hit; exact ⟨0,hit⟩
  · rename_i nonzero
    have equivalent : (∃ t, Hits (diagonal box t) excess) ↔
        ∃ t, SolvedProfiles.endpoint (box.map anchor) t ≤
          (2^(2^(cost (diagonal box 0)-excess)))^
            ((2^t)^(SolvedProfiles.freeCount (box.map anchor)))-1 := by
      constructor
      · intro ⟨t,hit⟩; exact ⟨t,(hits_diagonal_iff box excess t indexValid).mp hit⟩
      · intro ⟨t,hit⟩; exact ⟨t,(hits_diagonal_iff box excess t indexValid).mpr hit⟩
    rw [equivalent]
    exact SolvedProfiles.diagonal_criterion (box.map anchor) _ (Nat.two_pow_pos _) (by omega)

def decision (box : List Constraint) (excess : Nat) : Bool :=
  if SolvedProfiles.freeCount (box.map anchor)=0 then
    decide (excess ≤ cost (diagonal box 0) ∧
      eval (diagonal box 0) (fun _ => 1) 0 ≤ 2^(2^(cost (diagonal box 0)-excess))-1)
  else decide (SolvedProfiles.leading (box.map anchor) <
    2^(2^(cost (diagonal box 0)-excess)))

theorem decision_correct (box : List Constraint) (excess : Nat)
    (valid : Nonempty box) (indexValid : excess ≤ cost (diagonal box 0)) :
    decision box excess = true ↔ Meets box excess := by
  rw [ideal_criterion box excess valid indexValid]
  unfold decision
  split <;> simp only [decide_eq_true_eq, Hits]

def witnessBound (box : List Constraint) :=
  if SolvedProfiles.freeCount (box.map anchor)=0 then 0
  else SolvedProfiles.witnessShift (box.map anchor)

theorem witness_bound_hits (box : List Constraint) (excess : Nat)
    (indexValid : excess ≤ cost (diagonal box 0)) (accepted : decision box excess = true) :
    Hits (diagonal box (witnessBound box)) excess := by
  unfold decision at accepted
  unfold witnessBound
  split
  · rename_i zero
    simp only [if_pos zero,decide_eq_true_eq] at accepted
    exact accepted
  · rename_i nonzero
    simp only [if_neg nonzero,decide_eq_true_eq] at accepted
    apply (hits_diagonal_iff box excess _ indexValid).mpr
    exact SolvedProfiles.diagonal_witness (box.map anchor) _ (by omega) accepted

-- Search stops at the first successful test and never allocates a list of
-- all offsets. The last offset is a proved witness, not a numerical guess.
def scan (test : Nat → Bool) : Nat → Nat → Nat
  | 0,start => start
  | fuel+1,start => if test start then start else scan test fuel (start+1)

theorem scan_hits (test : Nat → Bool) (fuel start : Nat)
    (last : test (start+fuel)=true) : test (scan test fuel start)=true := by
  induction fuel generalizing start with
  | zero => simpa only [scan,Nat.add_zero] using last
  | succ fuel ih =>
    simp only [scan]
    split
    · assumption
    · apply ih
      have index : start+1+fuel=start+(fuel+1) := by omega
      rw [index]
      exact last

def hitTest (box : List Constraint) (excess t : Nat) : Bool :=
  decide (excess ≤ cost (diagonal box t) ∧
    eval (diagonal box t) (fun _ => 1) 0 ≤ 2^(2^(cost (diagonal box t)-excess))-1)

def witness (box : List Constraint) (excess : Nat) : Option (List Instr) :=
  if decision box excess then
    some (diagonal box (scan (hitTest box excess) (witnessBound box) 0))
  else none

theorem witness_sound (box : List Constraint) (excess : Nat)
    (valid : Nonempty box) (indexValid : excess ≤ cost (diagonal box 0))
    (code : List Instr) (found : witness box excess=some code) :
    Inside box code ∧ Hits code excess := by
  unfold witness at found
  split at found
  · rename_i accepted
    cases found
    refine ⟨diagonal_inside box _ valid,?_⟩
    have last := witness_bound_hits box excess indexValid accepted
    have scanned := scan_hits (hitTest box excess) (witnessBound box) 0
      (by simpa only [Nat.zero_add,hitTest,decide_eq_true_eq] using last)
    simpa only [hitTest,decide_eq_true_eq] using scanned
  · contradiction

theorem witness_empty (box : List Constraint) (excess : Nat)
    (valid : Nonempty box) (indexValid : excess ≤ cost (diagonal box 0))
    (empty : witness box excess=none) : ¬Meets box excess := by
  intro meets
  have accepted := (decision_correct box excess valid indexValid).mpr meets
  simp only [witness,accepted,if_true] at empty

end SolvedIdeal
