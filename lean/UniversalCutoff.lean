import ArithmeticBasis
import AdditiveSeparation

namespace SolvedUniversal
open SolvedBasis SolvedArithmeticBasis SolvedMarked SolvedInflation SolvedEncoding

def upto : Nat → List Nat
  | 0 => [0]
  | n+1 => (n+1)::upto n

theorem mem_upto (n x : Nat) : x ∈ upto n ↔ x ≤ n := by
  induction n with
  | zero => simp only [upto,List.mem_cons,List.not_mem_nil,or_false]; omega
  | succ n ih => simp only [upto,List.mem_cons,ih]; omega

def words {α : Type} (alphabet : List α) : Nat → List (List α)
  | 0 => [[]]
  | n+1 => alphabet.bind (fun a => (words alphabet n).map (List.cons a))

theorem mem_words {α : Type} (alphabet : List α) (n : Nat) (word : List α) :
    word ∈ words alphabet n ↔ word.length=n ∧ ∀ a, a ∈ word → a ∈ alphabet := by
  induction n generalizing word with
  | zero =>
    cases word with
    | nil => simp [words]
    | cons a tail => simp [words]
  | succ n ih =>
    simp only [words,SolvedLists.mem_bind,List.mem_map]
    constructor
    · intro ⟨a,member,tail,inside,same⟩
      subst word
      have facts := (ih tail).mp inside
      refine ⟨by simp only [List.length_cons,facts.1],?_⟩
      intro b belongs
      rcases List.mem_cons.mp belongs with equal | rest
      · exact equal ▸ member
      · exact facts.2 b rest
    · intro ⟨length,members⟩
      cases word with
      | nil => simp at length
      | cons a tail =>
        refine ⟨a,members a (List.Mem.head _),tail,?_,rfl⟩
        apply (ih tail).mpr
        exact ⟨by simp only [List.length_cons] at length; omega,
          fun b h => members b (List.Mem.tail _ h)⟩

def alphabet (C M : Nat) : List Cell :=
  (upto M).bind (fun a =>
    ((upto M).bind fun b => [Cell.add a b,Cell.mul a b]) ++
    (upto C).map (fun k => Cell.squares a (k+1)))

def boundedCells (C M : Nat) : List (List Cell) :=
  (upto M).bind (words (alphabet C M))

def table (cells : List Cell) : Template cells.length := cells.get

def baseProgram (cells : List Cell) := cells.map (fun c => instruction c 0)

theorem emit_cons (cell : Cell) (cells : List Cell) (p : Point cells.length) (extra : Nat) :
    emit (cell::cells).length (table (cell::cells)) (Fin.cases extra p) =
      instruction cell extra :: emit cells.length (table cells) p := by
  rfl

theorem base_program (cells : List Cell) :
    emit cells.length (table cells) (fun _ => 0)=baseProgram cells := by
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
    change instruction cell 0 :: emit cells.length (table cells) (fun _ => 0) =
      instruction cell 0 :: baseProgram cells
    rw [ih]

def clip (C : Nat) : List Instr → List Cell
  | [] => []
  | .add a b::tail => .add a b::clip C tail
  | .mul a b::tail => .mul a b::clip C tail
  | .sqRun a k::tail => .squares a (min k (C+1))::clip C tail

theorem clip_length (C : Nat) (code : List Instr) : (clip C code).length=code.length := by
  induction code with
  | nil => rfl
  | cons instr tail ih => cases instr <;> simp only [clip,List.length_cons,ih]

theorem clip_reconstruct (C : Nat) (code : List Instr) :
    ∃ p : Point (clip C code).length, emit (clip C code).length (table (clip C code)) p=code := by
  induction code with
  | nil => exact ⟨fun i => Fin.elim0 i,rfl⟩
  | cons instr tail ih =>
    obtain ⟨p,reconstructed⟩ := ih
    cases instr with
    | add a b =>
      refine ⟨Fin.cases 0 p,?_⟩
      simp only [clip,emit_cons,instruction,reconstructed]
    | mul a b =>
      refine ⟨Fin.cases 0 p,?_⟩
      simp only [clip,emit_cons,instruction,reconstructed]
    | sqRun a k =>
      refine ⟨Fin.cases (k-min k (C+1)) p,?_⟩
      have restoration : min k (C+1)+(k-min k (C+1))=k := by
        have := Nat.min_le_left k (C+1); omega
      simp only [clip,emit_cons,instruction,restoration,reconstructed]

theorem clip_cost_alternative (C : Nat) (code : List Instr) :
    cost (baseProgram (clip C code))=cost code ∨ C+1 ≤ cost (baseProgram (clip C code)) := by
  induction code with
  | nil => exact Or.inl rfl
  | cons instr tail ih =>
    cases instr with
    | add a b =>
      simp only [clip,baseProgram,List.map_cons,instruction,cost] at *
      omega
    | mul a b =>
      simp only [clip,baseProgram,List.map_cons,instruction,cost] at *
      omega
    | sqRun a k =>
      simp only [clip,baseProgram,List.map_cons,instruction,cost,Nat.add_zero] at *
      by_cases small : k ≤ C+1
      · rw [Nat.min_eq_left small]
        omega
      · rw [Nat.min_eq_right (by omega : C+1 ≤ k)]
        omega

theorem clip_admissible {C excess : Nat} {code : List Instr}
    (bounded : excess ≤ C) (enough : excess ≤ cost code) :
    excess ≤ cost (emit (clip C code).length (table (clip C code)) (fun _ => 0)) := by
  rw [base_program]
  have alternatives := clip_cost_alternative C code
  omega

def Positive : Cell → Prop
  | .squares _ base => 0 < base
  | _ => True

theorem table_valid (cells : List Cell) (positive : ∀ cell, cell ∈ cells → Positive cell) :
    Valid (table cells) := by
  intro i
  exact positive (cells.get i) (List.get_mem cells i.val i.isLt)

theorem clip_positive {C M : Nat} {code : List Instr} (fits : AllFits M code) :
    ∀ cell, cell ∈ clip C code → Positive cell := by
  induction code with
  | nil => intro cell member; cases member
  | cons instr tail ih =>
    intro cell member
    cases instr with
    | add a b =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell; trivial
      · exact ih fits.2 cell rest
    | mul a b =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell; trivial
      · exact ih fits.2 cell rest
    | sqRun a k =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell
        have lower := fits.1.2
        change 0 < min k (C+1)
        omega
      · exact ih fits.2 cell rest

theorem clip_alphabet {C M : Nat} {code : List Instr} (fits : AllFits M code) :
    ∀ cell, cell ∈ clip C code → cell ∈ alphabet C M := by
  induction code with
  | nil => intro cell member; cases member
  | cons instr tail ih =>
    intro cell member
    cases instr with
    | add a b =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell
        apply (SolvedLists.mem_bind _ _ _).mpr
        refine ⟨a,(mem_upto M a).mpr fits.1.1,?_⟩
        apply (SolvedLists.mem_append _ _ _).mpr
        apply Or.inl
        apply (SolvedLists.mem_bind _ _ _).mpr
        exact ⟨b,(mem_upto M b).mpr fits.1.2,List.Mem.head _⟩
      · exact ih fits.2 cell rest
    | mul a b =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell
        apply (SolvedLists.mem_bind _ _ _).mpr
        refine ⟨a,(mem_upto M a).mpr fits.1.1,?_⟩
        apply (SolvedLists.mem_append _ _ _).mpr
        apply Or.inl
        apply (SolvedLists.mem_bind _ _ _).mpr
        exact ⟨b,(mem_upto M b).mpr fits.1.2,List.Mem.tail _ (List.Mem.head _)⟩
      · exact ih fits.2 cell rest
    | sqRun a k =>
      rcases List.mem_cons.mp member with same | rest
      · subst cell
        apply (SolvedLists.mem_bind _ _ _).mpr
        refine ⟨a,(mem_upto M a).mpr fits.1.1,?_⟩
        apply (SolvedLists.mem_append _ _ _).mpr
        apply Or.inr
        apply List.mem_map.mpr
        have lower := fits.1.2
        refine ⟨min k (C+1)-1,(mem_upto C _).mpr (by omega),?_⟩
        have equal : min k (C+1)-1+1=min k (C+1) := by omega
        rw [equal]
      · exact ih fits.2 cell rest

theorem clip_enumerated {C M : Nat} {code : List Instr}
    (fits : AllFits M code) (size : code.length ≤ M) :
    clip C code ∈ boundedCells C M := by
  apply (SolvedLists.mem_bind _ _ _).mpr
  refine ⟨code.length,(mem_upto M _).mpr size,?_⟩
  exact (mem_words _ _ _).mpr ⟨clip_length C code,clip_alphabet fits⟩

def maximum (values : List Nat) : Nat := values.foldr max 0

theorem maximum_contains (values : List Nat) (n : Nat) (member : n ∈ values) :
    n ≤ maximum values := by
  induction values with
  | nil => cases member
  | cons a tail ih =>
    rcases List.mem_cons.mp member with same | rest
    · subst n; exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih rest) (Nat.le_max_right _ _)

def templateCutoff (cells : List Cell) (excess : Nat) : Option Nat :=
  if valid : Valid (table cells) then
    if indexValid : excess ≤ cost (emit cells.length (table cells) (fun _ => 0)) then
      some (cutoff (table cells) excess valid indexValid)
    else none
  else none

theorem template_cutoff_correct (cells : List Cell) (excess : Nat)
    (valid : Valid (table cells))
    (indexValid : excess ≤ cost (emit cells.length (table cells) (fun _ => 0)))
    (p : Point cells.length)
    (endpoint : eval (emit cells.length (table cells) p) (fun _ => 1) 0 =
      2^(2^(cost (emit cells.length (table cells) p)-excess))-1) :
    cost (emit cells.length (table cells) p)-excess < (templateCutoff cells excess).getD 0 := by
  simp only [templateCutoff,dif_pos valid,dif_pos indexValid,Option.getD]
  exact exact_below_cutoff (table cells) excess valid indexValid p endpoint

def portfolio (C : Nat) (candidates : List (List Cell)) :=
  maximum (candidates.bind fun cells => (upto C).map (fun excess => (templateCutoff cells excess).getD 0))

theorem portfolio_contains {C : Nat} {candidates : List (List Cell)}
    {cells : List Cell} {excess : Nat} (member : cells ∈ candidates) (bounded : excess ≤ C) :
    (templateCutoff cells excess).getD 0 ≤ portfolio C candidates := by
  apply maximum_contains
  apply (SolvedLists.mem_bind _ _ _).mpr
  refine ⟨cells,member,?_⟩
  exact List.mem_map.mpr ⟨excess,(mem_upto C excess).mpr bounded,rfl⟩

-- This finite definition is computable. Its exhaustive size is not claimed
-- to be practical, and the universal construction is not run by the tests.
def threshold (C : Nat) := max 1 (portfolio C (boundedCells C (12*C+13)))

theorem threshold_positive (C : Nat) : 1 ≤ threshold C := Nat.le_max_left _ _

theorem bounded_code_index {C M n excess : Nat} {code : List Instr}
    (fits : AllFits M code) (size : code.length ≤ M) (bounded : excess ≤ C)
    (costEq : cost code=n+excess)
    (endpoint : eval code (fun _ => 1) 0=2^(2^n)-1) :
    n < portfolio C (boundedCells C M) := by
  obtain ⟨p,reconstructed⟩ := clip_reconstruct C code
  have valid := table_valid (clip C code) (clip_positive fits)
  have indexValid := clip_admissible bounded (by omega : excess ≤ cost code)
  have target : eval (emit (clip C code).length (table (clip C code)) p) (fun _ => 1) 0 =
      2^(2^(cost (emit (clip C code).length (table (clip C code)) p)-excess))-1 := by
    rw [reconstructed,costEq,Nat.add_sub_cancel]
    exact endpoint
  have bound := template_cutoff_correct (clip C code) excess valid indexValid p target
  rw [reconstructed,costEq,Nat.add_sub_cancel] at bound
  exact Nat.lt_of_lt_of_le bound (portfolio_contains (clip_enumerated fits size) bounded)

theorem effective_chain_bound (C n : Nat) (above : threshold C ≤ n) {r : Nat}
    (chain : SolvedCoverage.Chain r) (endpoint : chain.value r=2^(2^n)-1) :
    n+C < r := by
  have positive : 1 ≤ n := Nat.le_trans (threshold_positive C) above
  by_cases short : r ≤ n+C
  · obtain ⟨code,_legal,fits,costEq,value,size⟩ :=
      mersenne_encoding chain positive endpoint short
    have lower : n ≤ r := by
      apply SolvedGrowth.level_requires_writes chain
      rw [endpoint]
      exact SolvedGrowth.mersenne_reaches_level positive
    have index := bounded_code_index fits size (by omega : r-n ≤ C)
      (by omega : cost code=n+(r-n)) value
    have bound : portfolio C (boundedCells C (12*C+13)) ≤ threshold C := Nat.le_max_right _ _
    omega
  · omega

theorem effective_program_bound (C n : Nat) (above : threshold C ≤ n) {r : Nat}
    (program : SolvedNormalization.Program r) (endpoint : program.value r=2^(2^n)-1) :
    n+C < r := by
  obtain ⟨length,chain,shorter,same⟩ := SolvedNormalization.normalize program
  have lower := effective_chain_bound C n above chain (same.trans endpoint)
  omega

theorem effective_additive_gap (C n : Nat) (above : threshold (C+2) ≤ n) {a b : Nat}
    (am : SolvedSeparation.MinimumAM (2^(2^n)-1) a)
    (slp : SolvedSeparation.MinimumSLP (2^(2^n)-1) b) : b+C<a := by
  obtain ⟨program,endpoint⟩ := am.1
  have lower := effective_program_bound (C+2) n above program endpoint
  have upper := slp.2 (n+2) (SolvedSeparation.mersenneProgram n)
    (SolvedSeparation.mersenneProgram_head n)
  omega

theorem effective_minima (C n : Nat) (above : threshold (C+2) ≤ n) :
    ∃ a b, SolvedSeparation.MinimumAM (2^(2^n)-1) a ∧
      SolvedSeparation.MinimumSLP (2^(2^n)-1) b ∧ b+C<a := by
  have positive : 1 ≤ 2^(2^n)-1 := by have := SolvedGrowth.tower_large n; omega
  obtain ⟨⟨a,am⟩,⟨b,slp⟩⟩ := SolvedSeparation.minima_exist _ positive
  exact ⟨a,b,am,slp,effective_additive_gap C n above am slp⟩

end SolvedUniversal
