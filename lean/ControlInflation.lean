import Compression
import MarkedComparison

namespace SolvedInflation
open SolvedMarked

abbrev lift := SolvedCompression.iterSq

theorem runs_agree (k x : Nat) : iterSq k x = lift k x := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [iterSq,lift,SolvedCompression.iterSq,ih]

theorem lift_comp (p q x : Nat) : lift (p+q) x = lift q (lift p x) :=
  SolvedCompression.iterSq_add p q x

theorem lift_multiplication (q x y : Nat) : lift q (x*y) = lift q x * lift q y :=
  SolvedCompression.iterSq_mul q x y

theorem lift_mono (k : Nat) {a b : Nat} (h : a ≤ b) : lift k a ≤ lift k b := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.mul_le_mul ih ih

theorem self_le_lift (k x : Nat) : x ≤ lift k x := by
  induction k with
  | zero => exact Nat.le_refl _
  | succ k ih => exact Nat.le_trans ih (self_le_sq (lift k x))

theorem lift_increase (q e x : Nat) : lift q x ≤ lift (q+e) x := by
  rw [lift_comp]
  exact self_le_lift e _

theorem lift_commute (p q x : Nat) : lift p (lift q x) = lift q (lift p x) := by
  rw [← lift_comp, ← lift_comp, Nat.add_comm q p]

theorem lift_add (q x y : Nat) : lift q x + lift q y ≤ lift q (x+y) := by
  induction q with
  | zero => exact Nat.le_refl _
  | succ q ih =>
    have lower := add_bound (Nat.le_refl (lift q x * lift q x))
      (Nat.le_refl (lift q y * lift q y))
    exact Nat.le_trans lower (Nat.mul_le_mul ih ih)

def PowerBound (q : Nat) (new old : Hist) : Prop := ∀ i, new i ≤ lift q (old i)

theorem weaken {q : Nat} {new old : Hist} (h : PowerBound q new old) (e : Nat) :
    PowerBound (q+e) new old := by
  intro i
  exact Nat.le_trans (h i) (lift_increase q e (old i))

theorem pushed {q a x : Nat} {new old : Hist}
    (ha : a ≤ lift q x) (h : PowerBound q new old) :
    PowerBound q (push a new) (push x old) := by
  intro i
  cases i with
  | zero => exact ha
  | succ i => exact h i

theorem unchanged_instruction (instr : Instr) {q : Nat} {new old : Hist}
    (h : PowerBound q new old) : PowerBound q (evalI instr new) (evalI instr old) := by
  cases instr with
  | add a b =>
    exact pushed (Nat.le_trans (Nat.add_le_add (h a) (h b)) (lift_add q _ _)) h
  | mul a b =>
    apply pushed ?_ h
    rw [lift_multiplication]
    exact Nat.mul_le_mul (h a) (h b)
  | sqRun a k =>
    apply pushed ?_ h
    rw [runs_agree,runs_agree]
    have grown := lift_mono k (h a)
    rw [lift_commute k q] at grown
    exact grown

theorem expanded_run (a k extra : Nat) {q : Nat} {new old : Hist}
    (h : PowerBound q new old) :
    PowerBound (q+extra) (evalI (.sqRun a (k+extra)) new) (evalI (.sqRun a k) old) := by
  apply pushed ?_ (weaken h extra)
  rw [runs_agree,runs_agree,lift_comp]
  have base := lift_mono k (h a)
  rw [lift_commute k q] at base
  have full := lift_mono extra base
  simpa only [lift_comp] using full

inductive Inflation : List Instr → List Instr → Nat → Prop
  | nil : Inflation [] [] 0
  | keep {old new : List Instr} {extra : Nat} (instr : Instr)
      (tail : Inflation old new extra) : Inflation (instr::old) (instr::new) extra
  | grow {old new : List Instr} {rest : Nat} (a k extra : Nat)
      (tail : Inflation old new rest) :
      Inflation (.sqRun a k::old) (.sqRun a (k+extra)::new) (extra+rest)

def cost : List Instr → Nat
  | [] => 0
  | .sqRun _ k::tail => k + cost tail
  | _::tail => 1 + cost tail

theorem inflation_cost {old new : List Instr} {extra : Nat}
    (h : Inflation old new extra) : cost new = cost old + extra := by
  induction h with
  | nil => rfl
  | keep instr _tail ih => cases instr <;> simp only [cost] at * <;> omega
  | grow a k extra _tail ih => simp only [cost]; omega

theorem inflation_evaluates {old new : List Instr} {extra q : Nat}
    (h : Inflation old new extra) {larger smaller : Hist} (bound : PowerBound q larger smaller) :
    PowerBound (q+extra) (eval new larger) (eval old smaller) := by
  induction h generalizing q larger smaller with
  | nil => exact bound
  | keep instr _tail ih => exact ih (unchanged_instruction instr bound)
  | grow a k extra _tail ih =>
    have start := expanded_run a k extra bound
    simpa only [eval,Nat.add_assoc] using ih start

theorem inflation_domination {old new : List Instr} {extra : Nat}
    (h : Inflation old new extra) (initial : Hist) :
    eval new initial 0 ≤ lift (cost new-cost old) (eval old initial 0) := by
  have reflexive : PowerBound 0 initial initial := fun _ => Nat.le_refl _
  have final := inflation_evaluates h reflexive 0
  have difference : cost new-cost old=extra := by
    rw [inflation_cost h]
    omega
  simpa only [difference,Nat.zero_add] using final



inductive Shape
  | add (a b : Nat)
  | mul (a b : Nat)
  | sq (a : Nat)
  deriving DecidableEq

def erase : List Instr → List Shape
  | [] => []
  | .add a b::tail => .add a b::erase tail
  | .mul a b::tail => .mul a b::erase tail
  | .sqRun a _::tail => .sq a::erase tail

def parameters : List Instr → List Nat
  | [] => []
  | .sqRun _ k::tail => k::parameters tail
  | _::tail => 0::parameters tail

inductive Below : List Nat → List Nat → Prop
  | nil : Below [] []
  | cons {a b : Nat} {xs ys : List Nat} (head : a ≤ b) (tail : Below xs ys) :
      Below (a::xs) (b::ys)

theorem comparable_inflation {old new : List Instr} (same : erase old = erase new)
    (ordered : Below (parameters old) (parameters new)) :
    ∃ extra, Inflation old new extra := by
  induction old generalizing new with
  | nil =>
    cases new with
    | nil => exact ⟨0,Inflation.nil⟩
    | cons instr tail => cases instr <;> simp [erase] at same
  | cons instr old ih =>
    cases new with
    | nil => cases instr <;> simp [erase] at same
    | cons other new =>
      cases instr with
      | add a b =>
        cases other with
        | add c d =>
          simp only [erase,List.cons.injEq,Shape.add.injEq] at same
          obtain ⟨⟨rfl,rfl⟩,sameTail⟩ := same
          cases ordered with
          | cons _ rest =>
            obtain ⟨extra,tail⟩ := ih sameTail rest
            exact ⟨extra,Inflation.keep (.add _ _) tail⟩
        | mul c d => simp [erase] at same
        | sqRun c k => simp [erase] at same
      | mul a b =>
        cases other with
        | mul c d =>
          simp only [erase,List.cons.injEq,Shape.mul.injEq] at same
          obtain ⟨⟨rfl,rfl⟩,sameTail⟩ := same
          cases ordered with
          | cons _ rest =>
            obtain ⟨extra,tail⟩ := ih sameTail rest
            exact ⟨extra,Inflation.keep (.mul _ _) tail⟩
        | add c d => simp [erase] at same
        | sqRun c k => simp [erase] at same
      | sqRun a k =>
        cases other with
        | sqRun c m =>
          simp only [erase,List.cons.injEq,Shape.sq.injEq] at same
          obtain ⟨rfl,sameTail⟩ := same
          cases ordered with
          | cons bound rest =>
            obtain ⟨extra,tail⟩ := ih sameTail rest
            have length : k+(m-k)=m := by omega
            refine ⟨m-k+extra,?_⟩
            simpa only [length] using Inflation.grow _ k (m-k) tail
        | add c d => simp [erase] at same
        | mul c d => simp [erase] at same

theorem comparable_domination {old new : List Instr} (same : erase old = erase new)
    (ordered : Below (parameters old) (parameters new)) (initial : Hist) :
    eval new initial 0 ≤ lift (cost new-cost old) (eval old initial 0) := by
  obtain ⟨extra,inflated⟩ := comparable_inflation same ordered
  exact inflation_domination inflated initial

end SolvedInflation
