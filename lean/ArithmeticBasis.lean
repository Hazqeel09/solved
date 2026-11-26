import FiniteBasis
import IdealOracle

namespace SolvedArithmeticBasis
open SolvedBasis SolvedMarked SolvedInflation

-- There is one coordinate per block. Coordinates of binary blocks are
-- ignored by evaluation and have zero in every minimal generator.
inductive Cell
  | add (a b : Nat)
  | mul (a b : Nat)
  | squares (a base : Nat)
  deriving Repr

abbrev Template (d : Nat) := Fin d → Cell

def instruction (cell : Cell) (extra : Nat) : Instr :=
  match cell with
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .squares a base => .sqRun a (base+extra)

def constraint (cell : Cell) (upper : Option Nat) : SolvedIdeal.Constraint :=
  match cell with
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .squares a base =>
    match upper with
    | none => .unbounded a base
    | some n => .bounded a base (base+n)

def emit : (d : Nat) → Template d → Point d → List Instr
  | 0,_,_ => []
  | d+1,template,p => instruction (template 0) (p 0) ::
      emit d (fun i => template i.succ) (fun i => p i.succ)

def request : (d : Nat) → Template d → Box d → List SolvedIdeal.Constraint
  | 0,_,_ => []
  | d+1,template,box => constraint (template 0) (box 0) ::
      request d (fun i => template i.succ) (fun i => box i.succ)

def Valid {d : Nat} (template : Template d) : Prop :=
  ∀ i, match template i with | .squares _ base => 0 < base | _ => True

instance {d : Nat} (template : Template d) : Decidable (Valid template) := by
  let checks : DecidablePred (fun i => match template i with
      | .squares _ base => 0 < base | _ => True) :=
    fun i => by dsimp; cases template i <;> infer_instance
  exact @Nat.decidableForallFin d _ checks

theorem request_valid {d : Nat} (template : Template d) (box : Box d)
    (valid : Valid template) : SolvedIdeal.Nonempty (request d template box) := by
  induction d with
  | zero => trivial
  | succ d ih =>
    have tail := ih (fun i => template i.succ) (fun i => box i.succ) (fun i => valid i.succ)
    have head := valid 0
    simp only [request]
    cases cell : template 0 with
    | add a b => exact tail
    | mul a b => exact tail
    | squares a base =>
      simp only [cell] at head
      cases bound : box 0 with
      | none =>
        simp only [constraint,bound,SolvedIdeal.Nonempty]
        exact ⟨head,tail⟩
      | some n =>
        simp only [constraint,bound,SolvedIdeal.Nonempty]
        exact ⟨head,by omega,tail⟩

theorem emit_inside {d : Nat} (template : Template d) (box : Box d) (p : Point d)
    (fits : Fits p box) : SolvedIdeal.Inside (request d template box) (emit d template p) := by
  induction d with
  | zero => exact SolvedIdeal.Inside.nil
  | succ d ih =>
    have tail := ih (fun i => template i.succ) (fun i => box i.succ) (fun i => p i.succ)
      (fun i => fits i.succ)
    have head := fits 0
    simp only [request,emit]
    cases _cell : template 0 with
    | add a b => exact SolvedIdeal.Inside.add a b tail
    | mul a b => exact SolvedIdeal.Inside.mul a b tail
    | squares a base =>
      cases bound : box 0 with
      | none =>
        simp only [constraint,bound,instruction]
        exact SolvedIdeal.Inside.unbounded a base (base+p 0) (by omega) tail
      | some n =>
        simp only [bound] at head
        simp only [constraint,bound,instruction]
        exact SolvedIdeal.Inside.bounded a base (base+n) (base+p 0) (by omega) (by omega) tail

theorem emit_cost_lower {d : Nat} (template : Template d) (p : Point d) :
    cost (emit d template (fun _ => 0)) ≤ cost (emit d template p) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have tail := ih (fun i => template i.succ) (fun i => p i.succ)
    cases cell : template 0 <;> simp only [emit,cell,instruction,cost,Nat.add_zero] <;> omega

theorem request_cost_lower {d : Nat} (template : Template d) (box : Box d) :
    cost (emit d template (fun _ => 0)) ≤ cost (SolvedIdeal.diagonal (request d template box) 0) := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    have tail := ih (fun i => template i.succ) (fun i => box i.succ)
    cases cell : template 0 with
    | add a b =>
      simpa only [emit,request,cell,constraint,instruction,SolvedIdeal.diagonal,
        List.map_cons,SolvedIdeal.anchor,SolvedProfiles.concrete,cost] using Nat.add_le_add_left tail 1
    | mul a b =>
      simpa only [emit,request,cell,constraint,instruction,SolvedIdeal.diagonal,
        List.map_cons,SolvedIdeal.anchor,SolvedProfiles.concrete,cost] using Nat.add_le_add_left tail 1
    | squares a base =>
      cases bound : box 0 <;>
        simp only [emit,request,cell,bound,constraint,instruction,SolvedIdeal.diagonal,
          List.map_cons,SolvedIdeal.anchor,SolvedProfiles.concrete,cost,Nat.add_zero] at * <;> omega

def recover : (d : Nat) → Template d → List Instr → Point d
  | 0,_,_ => fun i => Fin.elim0 i
  | d+1,template,code =>
    let first := match template 0,code with
      | .squares _ base,.sqRun _ k::_ => k-base
      | _,_ => 0
    let tail := match code with | [] => [] | _::tail => tail
    Fin.cases first (recover d (fun i => template i.succ) tail)

theorem recover_spec {d : Nat} (template : Template d) (box : Box d) (code : List Instr)
    (inside : SolvedIdeal.Inside (request d template box) code) :
    Fits (recover d template code) box ∧ emit d template (recover d template code)=code := by
  induction d generalizing code with
  | zero =>
    cases inside
    exact ⟨fun i => Fin.elim0 i,rfl⟩
  | succ d ih =>
    cases cell : template 0 with
    | add a b =>
      simp only [request,cell,constraint] at inside
      cases inside with
      | add _ _ tail =>
        have rest := ih (fun i => template i.succ) (fun i => box i.succ) _ tail
        constructor
        · intro i
          cases i using Fin.cases with
          | zero => cases bound : box 0 <;> simp only [recover,cell,Fin.cases_zero,bound]; omega
          | succ i => exact rest.1 i
        · simpa only [emit,recover,cell,Fin.cases_zero,Fin.cases_succ,instruction] using
            congrArg (List.cons (.add a b)) rest.2
    | mul a b =>
      simp only [request,cell,constraint] at inside
      cases inside with
      | mul _ _ tail =>
        have rest := ih (fun i => template i.succ) (fun i => box i.succ) _ tail
        constructor
        · intro i
          cases i using Fin.cases with
          | zero => cases bound : box 0 <;> simp only [recover,cell,Fin.cases_zero,bound]; omega
          | succ i => exact rest.1 i
        · simpa only [emit,recover,cell,Fin.cases_zero,Fin.cases_succ,instruction] using
            congrArg (List.cons (.mul a b)) rest.2
    | squares a base =>
      cases bound : box 0 with
      | none =>
        simp only [request,cell,constraint,bound] at inside
        cases inside with
        | unbounded _ _ k lower tail =>
          have rest := ih (fun i => template i.succ) (fun i => box i.succ) _ tail
          constructor
          · intro i
            cases i using Fin.cases with
            | zero => simp only [bound]
            | succ i => exact rest.1 i
          · have equal : base+(k-base)=k := by omega
            simpa only [emit,recover,cell,Fin.cases_zero,Fin.cases_succ,instruction,equal] using
              congrArg (List.cons (.sqRun a k)) rest.2
      | some n =>
        simp only [request,cell,constraint,bound] at inside
        cases inside with
        | bounded _ _ _ k lower upper tail =>
          have rest := ih (fun i => template i.succ) (fun i => box i.succ) _ tail
          constructor
          · intro i
            cases i using Fin.cases with
            | zero =>
              simp only [bound,recover,cell,Fin.cases_zero]
              exact Nat.sub_le_of_le_add (by omega)
            | succ i => exact rest.1 i
          · have equal : base+(k-base)=k := by omega
            simpa only [emit,recover,cell,Fin.cases_zero,Fin.cases_succ,instruction,equal] using
              congrArg (List.cons (.sqRun a k)) rest.2

def Hit {d : Nat} (template : Template d) (excess : Nat) (p : Point d) :=
  SolvedIdeal.Hits (emit d template p) excess

def query {d : Nat} (template : Template d) (excess : Nat) (box : Box d) : Option (Point d) :=
  (SolvedIdeal.witness (request d template box) excess).map (recover d template)

def oracle {d : Nat} (template : Template d) (excess : Nat) (valid : Valid template)
    (indexValid : excess ≤ cost (emit d template (fun _ => 0))) : Oracle (Hit template excess) where
  query := query template excess
  sound := by
    intro box p found
    have index := Nat.le_trans indexValid (request_cost_lower template box)
    unfold query at found
    cases answer : SolvedIdeal.witness (request d template box) excess with
    | none => simp only [answer,Option.map] at found
    | some code =>
      simp only [answer,Option.map,Option.some.injEq] at found
      have witness := SolvedIdeal.witness_sound (request d template box) excess
        (request_valid template box valid) index code answer
      have recovered := recover_spec template box code witness.1
      subst p
      refine ⟨?_,recovered.1⟩
      change SolvedIdeal.Hits (emit d template (recover d template code)) excess
      rw [recovered.2]
      exact witness.2
  empty := by
    intro box answer p fits hit
    have index := Nat.le_trans indexValid (request_cost_lower template box)
    have empty : SolvedIdeal.witness (request d template box) excess = none := by
      unfold query at answer
      cases h : SolvedIdeal.witness (request d template box) excess with
      | none => rfl
      | some code => simp only [h,Option.map] at answer
    exact SolvedIdeal.witness_empty (request d template box) excess
      (request_valid template box valid) index empty
      ⟨emit d template p,emit_inside template box p fits,hit⟩

def minimalBasis {d : Nat} (template : Template d) (excess : Nat) (valid : Valid template)
    (indexValid : excess ≤ cost (emit d template (fun _ => 0))) :=
  SolvedBasis.basis (oracle template excess valid indexValid) (fun _ => none)

theorem minimal_basis_correct {d : Nat} (template : Template d) (excess : Nat)
    (valid : Valid template) (indexValid : excess ≤ cost (emit d template (fun _ => 0))) :
    (∀ p, p ∈ minimalBasis template excess valid indexValid → Minimal (Hit template excess) p) ∧
    (∀ x, Hit template excess x → Covered (minimalBasis template excess valid indexValid) x) := by
  have correct := basis_spec (oracle template excess valid indexValid) (fun _ => none)
  exact ⟨fun p member => (correct.1 p member).1,fun x hit => correct.2 x hit (fun _ => True.intro)⟩

theorem emit_comparable {d : Nat} (template : Template d) {p q : Point d}
    (ordered : Below p q) :
    erase (emit d template p)=erase (emit d template q) ∧
    SolvedInflation.Below (parameters (emit d template p)) (parameters (emit d template q)) := by
  induction d with
  | zero => exact ⟨rfl,SolvedInflation.Below.nil⟩
  | succ d ih =>
    have tail := ih (fun i => template i.succ) (fun i => ordered i.succ)
    have head := ordered 0
    cases cell : template 0 <;>
      simp only [emit,cell,instruction,erase,parameters]
    · exact ⟨congrArg (List.cons (.add _ _)) tail.1,SolvedInflation.Below.cons (Nat.le_refl _) tail.2⟩
    · exact ⟨congrArg (List.cons (.mul _ _)) tail.1,SolvedInflation.Below.cons (Nat.le_refl _) tail.2⟩
    · exact ⟨congrArg (List.cons (.sq _)) tail.1,SolvedInflation.Below.cons (by omega) tail.2⟩

theorem exact_cost_unchanged {old new : List Instr} {excess : Nat}
    (same : erase old=erase new)
    (ordered : SolvedInflation.Below (parameters old) (parameters new))
    (hit : SolvedIdeal.Hits old excess)
    (exactValue : eval new (fun _ => 1) 0=2^(2^(cost new-excess))-1) :
    cost old=cost new := by
  obtain ⟨extra,inflated⟩ := comparable_inflation same ordered
  have costs := inflation_cost inflated
  by_cases zero : extra=0
  · omega
  · have q : extra=(extra-1)+1 := by omega
    have domination := inflation_domination inflated (fun _ => 1)
    have difference : cost new-cost old=extra := by omega
    rw [difference,q] at domination
    have large : 2 ≤ SolvedCompression.iterSq (cost old-excess) 2 := by
      rw [← SolvedGrowth.tower_as_squares]
      exact SolvedGrowth.tower_large _
    have base : eval old (fun _ => 1) 0 ≤ SolvedCompression.iterSq (cost old-excess) 2-1 := by
      rw [← SolvedGrowth.tower_as_squares]; exact hit.2
    have excluded := SolvedSubtraction.exclusion_by_growth (extra-1) large base domination
    have index : cost old-excess+((extra-1)+1)=cost new-excess := by have := hit.1; omega
    rw [index, ← SolvedGrowth.tower_as_squares, exactValue] at excluded
    exact False.elim (Nat.lt_irrefl _ excluded)

def upperIndex {d : Nat} (template : Template d) (excess : Nat) : List (Point d) → Nat
  | [] => 0
  | p::tail => max (cost (emit d template p)-excess+1) (upperIndex template excess tail)

theorem member_index_bound {d : Nat} (template : Template d) (excess : Nat)
    (points : List (Point d)) (p : Point d) (member : p ∈ points) :
    cost (emit d template p)-excess < upperIndex template excess points := by
  induction points with
  | nil => cases member
  | cons q tail ih =>
    rcases List.mem_cons.mp member with same | inside
    · subst p
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (ih inside) (Nat.le_max_right _ _)

def cutoff {d : Nat} (template : Template d) (excess : Nat) (valid : Valid template)
    (indexValid : excess ≤ cost (emit d template (fun _ => 0))) :=
  upperIndex template excess (minimalBasis template excess valid indexValid)

theorem exact_below_cutoff {d : Nat} (template : Template d) (excess : Nat)
    (valid : Valid template) (indexValid : excess ≤ cost (emit d template (fun _ => 0)))
    (p : Point d)
    (exactValue : eval (emit d template p) (fun _ => 1) 0 =
      2^(2^(cost (emit d template p)-excess))-1) :
    cost (emit d template p)-excess < cutoff template excess valid indexValid := by
  have own : Hit template excess p :=
    ⟨Nat.le_trans indexValid (emit_cost_lower template p),Nat.le_of_eq exactValue⟩
  have correct := minimal_basis_correct template excess valid indexValid
  obtain ⟨q,member,ordered⟩ := correct.2 p own
  have qhit := (correct.1 q member).1
  have comparable := emit_comparable template ordered
  have costs := exact_cost_unchanged comparable.1 comparable.2 qhit exactValue
  have bound := member_index_bound template excess _ q member
  simpa only [costs] using bound

end SolvedArithmeticBasis
