import NonsquareBound
import ControlInflation

namespace SolvedEncoding
open SolvedCoverage SolvedMarked SolvedInflation

def extras {r : Nat} (c : Chain r) : Nat → List Nat
  | 0 => []
  | k+1 => if c.value (k+1)=c.value k*c.value k then extras c k
      else (k+1)::c.left (k+1)::c.right (k+1)::extras c k

def stock {r : Nat} (c : Chain r) : List Nat := r::extras c r

theorem extras_length {r : Nat} (c : Chain r) (k : Nat) :
    (extras c k).length = 3*SolvedGrowth.nonsquares c k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [extras,SolvedGrowth.nonsquares]
    split <;> simp only [List.length_cons,ih] <;> omega

theorem stock_length {r : Nat} (c : Chain r) :
    (stock c).length = 1+3*SolvedGrowth.nonsquares c r := by
  simp only [stock,List.length_cons,extras_length]
  omega

theorem extras_contains {r : Nat} (c : Chain r) (k : Nat) {j x : Nat}
    (positive : 0 < j) (bound : j ≤ k) (non : ¬ Square c j)
    (source : x=j ∨ c.left j=x ∨ c.right j=x) : x ∈ extras c k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : j=k+1
    · subst j
      have ne : ¬c.value (k+1)=c.value k*c.value k := by
        simpa only [Square,Nat.add_sub_cancel] using non
      simp only [extras,ne,if_false,List.mem_cons]
      rcases source with eq | eq | eq
      · exact Or.inl eq
      · exact Or.inr (Or.inl eq.symm)
      · exact Or.inr (Or.inr (Or.inl eq.symm))
    · have earlier := ih (by omega)
      simp only [extras]
      split
      · exact earlier
      · simp only [List.mem_cons]
        exact Or.inr (Or.inr (Or.inr earlier))

theorem stock_contains {r : Nat} (c : Chain r) {j : Nat}
    (positive : 0 < j) (mark : Marked c j) : j ∈ stock c := by
  simp only [stock,List.mem_cons]
  rcases mark with zero | final | own | operand
  · omega
  · subst j; exact Or.inl rfl
  · obtain ⟨pos,bound,non⟩ := own
    exact Or.inr (extras_contains c r pos bound non (Or.inl rfl))
  · obtain ⟨k,pos,bound,non,side⟩ := operand
    exact Or.inr (extras_contains c r pos bound non (Or.inr side))

inductive Remove (x : Nat) : List Nat → List Nat → Prop
  | head (tail : List Nat) : Remove x (x::tail) tail
  | keep {before after : List Nat} (y : Nat) (rest : Remove x before after) :
      Remove x (y::before) (y::after)

theorem remove_exists {x : Nat} {before : List Nat} (member : x ∈ before) :
    ∃ after, Remove x before after := by
  induction before with
  | nil => cases member
  | cons y before ih =>
    cases member with
    | head => exact ⟨before,Remove.head before⟩
    | tail _ tail =>
      obtain ⟨after,removed⟩ := ih tail
      exact ⟨y::after,Remove.keep y removed⟩

theorem remove_length {x : Nat} {before after : List Nat} (h : Remove x before after) :
    before.length = after.length+1 := by
  induction h with
  | head tail => rfl
  | keep y rest ih => simp only [List.length_cons]; omega

theorem remove_preserves {x y : Nat} {before after : List Nat}
    (h : Remove x before after) (different : y ≠ x) (member : y ∈ before) : y ∈ after := by
  induction h with
  | head tail =>
    simp only [List.mem_cons] at member
    cases member with
    | inl eq => exact False.elim (different eq)
    | inr remains => exact remains
  | keep z _rest ih =>
    simp only [List.mem_cons]
    simp only [List.mem_cons] at member
    cases member with
    | inl eq => exact Or.inl eq
    | inr remains => exact Or.inr (ih remains)

def Fits (bound : Nat) : Instr → Prop
  | .add a b => a ≤ bound ∧ b ≤ bound
  | .mul a b => a ≤ bound ∧ b ≤ bound
  | .sqRun a k => a ≤ bound ∧ 1 ≤ k

def AllFits (bound : Nat) : List Instr → Prop
  | [] => True
  | instr::tail => Fits bound instr ∧ AllFits bound tail

inductive Legal : List Instr → Prop
  | nil : Legal []
  | snoc {code : List Instr} (previous : Legal code) (instr : Instr)
      (fits : Fits code.length instr) : Legal (code++[instr])

theorem fits_weaken {a b : Nat} (h : a ≤ b) (instr : Instr) (fits : Fits a instr) :
    Fits b instr := by
  cases instr <;> simp only [Fits] at * <;> omega

theorem allFits_weaken {a b : Nat} (h : a ≤ b) {code : List Instr}
    (fits : AllFits a code) : AllFits b code := by
  induction code with
  | nil => trivial
  | cons instr tail ih => exact ⟨fits_weaken h instr fits.1,ih fits.2⟩

theorem allFits_snoc {bound : Nat} (code : List Instr) (instr : Instr)
    (old : AllFits bound code) (next : Fits bound instr) : AllFits bound (code++[instr]) := by
  induction code with
  | nil => exact ⟨next,True.intro⟩
  | cons first rest ih => exact ⟨old.1,ih old.2⟩

theorem eval_snoc (code : List Instr) (instr : Instr) (initial : Hist) :
    eval (code++[instr]) initial = evalI instr (eval code initial) := by
  induction code generalizing initial with
  | nil => rfl
  | cons first _rest ih => exact ih (evalI first initial)

theorem cost_snoc (code : List Instr) (instr : Instr) :
    cost (code++[instr]) = cost code + cost [instr] := by
  induction code with
  | nil => simp [cost]
  | cons first rest ih =>
    cases first <;> simp only [List.cons_append,cost,List.append_eq] <;> rw [ih] <;> omega

theorem evalI_preserves_tail (instr : Instr) (history : Hist) (k : Nat) :
    evalI instr history (k+1) = history k := by
  cases instr <;> rfl



def initial : Hist := fun _ => 1

structure Scan {r : Nat} (c : Chain r) (position : Nat) where
  code : List Instr
  cursor : Nat
  pending : Nat
  rest : List Nat
  time_eq : cursor+pending=position
  cost_eq : cost code=cursor
  head_eq : eval code initial 0=c.value cursor
  available : ∀ j, j ≤ position → Marked c j →
    ∃ slot, slot < code.length+1 ∧ eval code initial slot=c.value j
  unmarked : ∀ j, cursor < j → j ≤ position → ¬ Marked c j
  future : ∀ j, position < j → j ≤ r → Marked c j → j ∈ rest
  size_eq : code.length+rest.length=(stock c).length
  legal : Legal code
  bounded : AllFits code.length code

theorem initial_scan {r : Nat} (c : Chain r) : Nonempty (Scan c 0) := by
  refine ⟨{
    code := []
    cursor := 0
    pending := 0
    rest := stock c
    time_eq := rfl
    cost_eq := rfl
    head_eq := ?_
    available := ?_
    unmarked := ?_
    future := ?_
    size_eq := by simp
    legal := Legal.nil
    bounded := True.intro
  }⟩
  · exact c.initial.symm
  · intro j bound _mark
    have zero : j=0 := by omega
    subst j
    exact ⟨0,by decide,c.initial.symm⟩
  · intro j lower upper
    omega
  · intro j positive _bound marked
    exact stock_contains c positive marked

theorem advance_unmarked {r i : Nat} {c : Chain r} (s : Scan c i)
    (absent : ¬ Marked c (i+1)) : Nonempty (Scan c (i+1)) := by
  refine ⟨{
    code := s.code
    cursor := s.cursor
    pending := s.pending+1
    rest := s.rest
    time_eq := ?_
    cost_eq := s.cost_eq
    head_eq := s.head_eq
    available := ?_
    unmarked := ?_
    future := ?_
    size_eq := s.size_eq
    legal := s.legal
    bounded := s.bounded
  }⟩
  · have position := s.time_eq
    omega
  · intro j bound mark
    have earlier : j ≤ i := by
      by_cases current : j=i+1
      · subst j; exact False.elim (absent mark)
      · omega
    exact s.available j earlier mark
  · intro j lower upper mark
    by_cases current : j=i+1
    · subst j; exact absent mark
    · exact s.unmarked j lower (by omega) mark
  · intro j lower upper mark
    exact s.future j (by omega) upper mark

theorem append_scan {r i : Nat} {c : Chain r} (s : Scan c i)
    (instr : Instr) (after : List Nat) (removed : Remove (i+1) s.rest after)
    (fits : Fits s.code.length instr) (spent : cost [instr]=s.pending+1)
    (produced : evalI instr (eval s.code initial) 0=c.value (i+1)) :
    Nonempty (Scan c (i+1)) := by
  have length : (s.code++[instr]).length=s.code.length+1 := by simp
  refine ⟨{
    code := s.code++[instr]
    cursor := i+1
    pending := 0
    rest := after
    time_eq := by omega
    cost_eq := ?_
    head_eq := ?_
    available := ?_
    unmarked := ?_
    future := ?_
    size_eq := ?_
    legal := Legal.snoc s.legal instr fits
    bounded := ?_
  }⟩
  · rw [cost_snoc,s.cost_eq,spent]
    have position := s.time_eq
    omega
  · rw [eval_snoc]
    exact produced
  · intro j bound mark
    by_cases current : j=i+1
    · subst j
      refine ⟨0,by omega,?_⟩
      rw [eval_snoc]
      exact produced
    · obtain ⟨slot,slotBound,value⟩ := s.available j (by omega) mark
      refine ⟨slot+1,?_,?_⟩
      · rw [length]
        omega
      · rw [eval_snoc,evalI_preserves_tail]
        exact value
  · intro j lower upper
    omega
  · intro j lower upper mark
    exact remove_preserves removed (by omega) (s.future j (by omega) upper mark)
  · rw [length]
    have old := s.size_eq
    have reduction := remove_length removed
    omega
  · rw [length]
    exact allFits_snoc s.code instr
      (allFits_weaken (by omega : s.code.length ≤ s.code.length+1) s.bounded)
      (fits_weaken (by omega : s.code.length ≤ s.code.length+1) instr fits)

theorem advance_marked {r i : Nat} {c : Chain r} (s : Scan c i)
    (bound : i+1 ≤ r) (mark : Marked c (i+1)) : Nonempty (Scan c (i+1)) := by
  obtain ⟨after,removed⟩ := remove_exists (s.future (i+1) (by omega) bound mark)
  by_cases sq : Square c (i+1)
  · have position := s.time_eq
    have endpoint : s.cursor+(s.pending+1)=i+1 := by omega
    have repeated := square_run c s.cursor (s.pending+1) (by omega) (by
      intro j lower upper
      by_cases current : j=i+1
      · subst j; exact sq
      · apply unmarked_is_square c (by omega) (by omega)
        exact s.unmarked j lower (by omega))
    rw [endpoint] at repeated
    apply append_scan s (.sqRun 0 (s.pending+1)) after removed
    · constructor <;> omega
    · simp [cost]
    · change SolvedMarked.iterSq (s.pending+1) (eval s.code initial 0)=c.value (i+1)
      rw [s.head_eq,runs_agree]
      exact repeated.symm
  · have predecessor : Marked c i := by
      simpa only [Nat.add_sub_cancel] using predecessor_marked c (by omega : 0<i+1) bound sq
    have position := s.time_eq
    have cursor : s.cursor=i := by
      by_cases gap : s.cursor<i
      · exact False.elim (s.unmarked i gap (Nat.le_refl _) predecessor)
      · omega
    have pending : s.pending=0 := by omega
    obtain ⟨leftBound,rightBound,recipe⟩ := c.valid (i+1) (by omega) bound
    have leftMarked : Marked c (c.left (i+1)) :=
      Or.inr (Or.inr (Or.inr ⟨i+1,by omega,bound,sq,Or.inl rfl⟩))
    have rightMarked : Marked c (c.right (i+1)) :=
      Or.inr (Or.inr (Or.inr ⟨i+1,by omega,bound,sq,Or.inr rfl⟩))
    obtain ⟨a,abound,avalue⟩ := s.available (c.left (i+1)) (by omega) leftMarked
    obtain ⟨b,bbound,bvalue⟩ := s.available (c.right (i+1)) (by omega) rightMarked
    cases flag : c.isMul (i+1)
    · apply append_scan s (.add a b) after removed
      · constructor <;> omega
      · simp [cost,pending]
      · change eval s.code initial a + eval s.code initial b=c.value (i+1)
        rw [avalue,bvalue]
        simp only [flag,Bool.false_eq_true,if_false] at recipe
        exact recipe.symm
    · apply append_scan s (.mul a b) after removed
      · constructor <;> omega
      · simp [cost,pending]
      · change eval s.code initial a * eval s.code initial b=c.value (i+1)
        rw [avalue,bvalue]
        simp only [flag,if_true] at recipe
        exact recipe.symm

theorem scan_exists {r : Nat} (c : Chain r) (i : Nat) (bound : i ≤ r) :
    Nonempty (Scan c i) := by
  induction i with
  | zero => exact initial_scan c
  | succ i ih =>
    obtain ⟨s⟩ := ih (by omega)
    by_cases mark : Marked c (i+1)
    · exact advance_marked s bound mark
    · exact advance_unmarked s mark

theorem complete_encoding {r : Nat} (c : Chain r) :
    ∃ code : List Instr, Legal code ∧ AllFits code.length code ∧
      cost code=r ∧ eval code initial 0=c.value r ∧
      code.length ≤ 3*SolvedGrowth.nonsquares c r+1 := by
  obtain ⟨s⟩ := scan_exists c r (Nat.le_refl _)
  have finalMarked : Marked c r := Or.inr (Or.inl rfl)
  have position := s.time_eq
  have cursor : s.cursor=r := by
    by_cases gap : s.cursor<r
    · exact False.elim (s.unmarked r gap (Nat.le_refl _) finalMarked)
    · omega
  have costValue : cost s.code=r := s.cost_eq.trans cursor
  have value : eval s.code initial 0=c.value r := by rw [s.head_eq,cursor]
  have size := s.size_eq
  rw [stock_length] at size
  exact ⟨s.code,s.legal,s.bounded,costValue,value,by omega⟩



theorem mersenne_encoding {r n excess : Nat} (c : Chain r)
    (positive : 1 ≤ n) (endpoint : c.value r=2^(2^n)-1)
    (budget : r ≤ n+excess) :
    ∃ code : List Instr, Legal code ∧ AllFits (12*excess+13) code ∧
      cost code=r ∧ eval code initial 0=2^(2^n)-1 ∧ code.length ≤ 12*excess+13 := by
  obtain ⟨code,legal,bounded,costEq,valueEq,lengthBound⟩ := complete_encoding c
  have count := SolvedGrowth.mersenne_nonsquare_bound c positive endpoint budget
  have size : code.length ≤ 12*excess+13 := by omega
  exact ⟨code,legal,allFits_weaken size bounded,costEq,valueEq.trans endpoint,size⟩

end SolvedEncoding
