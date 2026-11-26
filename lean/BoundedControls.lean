import MarkedEncoding
import SubtractionGap

namespace SolvedBounded
open SolvedMarked SolvedInflation SolvedEncoding

def lookup : List Instr → Nat → Option Instr
  | [], _ => none
  | instr::_, 0 => some instr
  | _::tail, k+1 => lookup tail k

def tag (code : List Instr) (k : Nat) : Nat :=
  match lookup code k with
  | none => 0
  | some (.add _ _) => 1
  | some (.mul _ _) => 2
  | some (.sqRun _ _) => 3

def leftField (code : List Instr) (k : Nat) : Nat :=
  match lookup code k with
  | none => 0
  | some (.add a _) | some (.mul a _) | some (.sqRun a _) => a

def rightField (code : List Instr) (k : Nat) : Nat :=
  match lookup code k with
  | some (.add _ b) | some (.mul _ b) => b
  | _ => 0

def runField (code : List Instr) (k : Nat) : Nat :=
  match lookup code k with
  | some (.sqRun _ n) => n
  | _ => 0

theorem lookup_outside (code : List Instr) (k : Nat) (outside : code.length ≤ k) :
    lookup code k=none := by
  induction code generalizing k with
  | nil => rfl
  | cons instr tail ih =>
    cases k with
    | zero => simp only [List.length_cons] at outside; omega
    | succ k => exact ih k (by simp only [List.length_cons] at outside; omega)

theorem tag_bound (code : List Instr) (k : Nat) : tag code k ≤ 3 := by
  induction code generalizing k with
  | nil => simp [tag,lookup]
  | cons instr tail ih =>
    cases k with
    | zero => cases instr <;> simp [tag,lookup]
    | succ k => exact ih k

theorem address_bounds {M : Nat} {code : List Instr} (fits : AllFits M code) (k : Nat) :
    leftField code k ≤ M ∧ rightField code k ≤ M := by
  induction code generalizing k with
  | nil => simp [leftField,rightField,lookup]
  | cons instr tail ih =>
    cases k with
    | zero => cases instr <;> simp only [AllFits,Fits] at fits <;>
        simp only [leftField,rightField,lookup] <;> omega
    | succ k => exact ih fits.2 k

theorem erase_length (code : List Instr) : (erase code).length=code.length := by
  induction code with
  | nil => rfl
  | cons instr tail ih => cases instr <;> simp [erase,ih]

theorem shape_from_fields {old new : List Instr}
    (tags : ∀ k, tag old k=tag new k)
    (lefts : ∀ k, leftField old k=leftField new k)
    (rights : ∀ k, rightField old k=rightField new k) : erase old=erase new := by
  induction old generalizing new with
  | nil =>
    cases new with
    | nil => rfl
    | cons instr tail => have h := tags 0; cases instr <;> simp [tag,lookup] at h
  | cons instr old ih =>
    cases new with
    | nil => have h := tags 0; cases instr <;> simp [tag,lookup] at h
    | cons other new =>
      have tail := ih (new := new) (fun k => tags (k+1))
        (fun k => lefts (k+1)) (fun k => rights (k+1))
      have headTag := tags 0
      have headLeft := lefts 0
      have headRight := rights 0
      cases instr <;> cases other <;>
        simp only [tag,leftField,rightField,lookup] at headTag headLeft headRight
      all_goals try omega
      all_goals simp only [erase,headLeft,headRight,tail]

theorem below_from_fields {old new : List Instr} (lengths : old.length=new.length)
    (ordered : ∀ k, runField old k ≤ runField new k) :
    Below (parameters old) (parameters new) := by
  induction old generalizing new with
  | nil =>
    cases new with
    | nil => exact Below.nil
    | cons instr tail => simp at lengths
  | cons instr old ih =>
    cases new with
    | nil => simp at lengths
    | cons other new =>
      have tailLength : old.length=new.length := by
        simp only [List.length_cons] at lengths
        omega
      have tail := ih tailLength (fun k => ordered (k+1))
      have head := ordered 0
      cases instr <;> cases other <;> exact Below.cons head tail

def fields (code : List Instr) (M j : Nat) : Nat → Nat
  | 0 => tag code j
  | 1 => 3-tag code j
  | 2 => leftField code j
  | 3 => M-leftField code j
  | 4 => rightField code j
  | 5 => M-rightField code j
  | _ => runField code j

def coordinates (code : List Instr) (excess C M k : Nat) : Nat :=
  if k=0 then excess else if k=1 then C-excess
  else fields code M ((k-2)/7) ((k-2)%7)

theorem coordinates_at (code : List Instr) (excess C M j slot : Nat) (small : slot<7) :
    coordinates code excess C M (7*j+slot+2)=fields code M j slot := by
  have first : 7*j+slot+2 ≠ 0 := by omega
  have second : 7*j+slot+2 ≠ 1 := by omega
  have position : (7*j+slot+2-2)/7=j := by omega
  have remainder : (7*j+slot+2-2)%7=slot := by omega
  simp only [coordinates,first,second,if_false,position,remainder]

theorem packed_comparison (old new : List Instr) (a b C M : Nat)
    (old_length : old.length ≤ M) (new_length : new.length ≤ M)
    (old_fits : AllFits M old) (new_fits : AllFits M new)
    (ab : a ≤ C) (bb : b ≤ C)
    (ordered : ∀ k, k < 2+7*M → coordinates old a C M k ≤ coordinates new b C M k) :
    a=b ∧ erase old=erase new ∧ Below (parameters old) (parameters new) := by
  have direct : a ≤ b := ordered 0 (by omega)
  have reverse : C-a ≤ C-b := ordered 1 (by omega)
  have excess : a=b := by omega
  have field_order (j slot : Nat) (position : j<M) (small : slot<7) :
      fields old M j slot ≤ fields new M j slot := by
    have bound := ordered (7*j+slot+2) (by omega)
    rw [coordinates_at old a C M j slot small, coordinates_at new b C M j slot small] at bound
    exact bound
  have point (j : Nat) : tag old j=tag new j ∧ leftField old j=leftField new j ∧
      rightField old j=rightField new j ∧ runField old j ≤ runField new j := by
    by_cases inside : j<M
    · have t0 := field_order j 0 inside (by decide)
      have t1 := field_order j 1 inside (by decide)
      have a0 := field_order j 2 inside (by decide)
      have a1 := field_order j 3 inside (by decide)
      have b0 := field_order j 4 inside (by decide)
      have b1 := field_order j 5 inside (by decide)
      have p := field_order j 6 inside (by decide)
      have ot := tag_bound old j
      have nt := tag_bound new j
      have oa := address_bounds old_fits j
      have na := address_bounds new_fits j
      simp only [fields] at t0 t1 a0 a1 b0 b1 p
      exact ⟨by omega,by omega,by omega,p⟩
    · have old_none := lookup_outside old j (by omega)
      have new_none := lookup_outside new j (by omega)
      simp [tag,leftField,rightField,runField,old_none,new_none]
  have same := shape_from_fields (fun j => (point j).1) (fun j => (point j).2.1)
    (fun j => (point j).2.2.1)
  have lengths : old.length=new.length := by rw [← erase_length old, ← erase_length new,same]
  exact ⟨excess,same,below_from_fields lengths (fun j => (point j).2.2.2)⟩



theorem bounded_programs_obstruction
    (code : Nat → List Instr) (index excess : Nat → Nat) (initial : Hist) (C M : Nat)
    (rising : ∀ i j, i<j → index i<index j)
    (sizes : ∀ i, (code i).length ≤ M) (fits : ∀ i, AllFits M (code i))
    (bounded : ∀ i, excess i ≤ C)
    (costs : ∀ i, cost (code i)=index i+excess i)
    (values : ∀ i, eval (code i) initial 0=2^(2^(index i))-1) : False := by
  let vector := fun i k => coordinates (code i) (excess i) C M k
  obtain ⟨g,increase,ordered⟩ := SolvedControls.thin vector (2+7*M)
  let i := g 0
  let j := g 1
  have ij : i<j := increase 0 1 (by decide)
  have comparison := packed_comparison (code i) (code j) (excess i) (excess j) C M
    (sizes i) (sizes j) (fits i) (fits j) (bounded i) (bounded j)
    (fun k hk => ordered k hk 0 1 (by decide))
  have newCost : cost (code j)=index j+excess i := by
    rw [comparison.1]
    exact costs j
  exact SolvedSubtraction.mersenne_program_antichain (code i) (code j) initial
    (index i) (index j) (excess i) (rising i j ij) comparison.2.1 comparison.2.2
    (costs i) newCost (values i) (values j)

theorem short_chain_sequence_impossible (index lengths : Nat → Nat)
    (family : ∀ i, SolvedCoverage.Chain (lengths i)) (C : Nat)
    (positive : ∀ i, 1 ≤ index i) (rising : ∀ i j, i<j → index i<index j)
    (endpoints : ∀ i, (family i).value (lengths i)=2^(2^(index i))-1)
    (budgets : ∀ i, lengths i ≤ index i+C) : False := by
  let encoded := fun i => SolvedEncoding.mersenne_encoding (family i) (positive i)
    (endpoints i) (budgets i)
  let code := fun i => Classical.choose (encoded i)
  have specification (i : Nat) := Classical.choose_spec (encoded i)
  let excess := fun i => lengths i-index i
  have lower (i : Nat) : index i ≤ lengths i := by
    apply SolvedGrowth.level_requires_writes (family i)
    rw [endpoints i]
    exact SolvedGrowth.mersenne_reaches_level (positive i)
  have costs (i : Nat) : cost (code i)=index i+excess i := by
    have actual : cost (code i)=lengths i := (specification i).2.2.1
    have atLeast := lower i
    change cost (code i)=index i+(lengths i-index i)
    omega
  have bounded (i : Nat) : excess i ≤ C := by
    have bound := budgets i
    change lengths i-index i ≤ C
    omega
  exact bounded_programs_obstruction code index excess SolvedEncoding.initial C (12*C+13)
    rising (fun i => (specification i).2.2.2.2) (fun i => (specification i).2.1)
    bounded costs (fun i => (specification i).2.2.2.1)

def ShortChain (n excess : Nat) : Prop :=
  ∃ r, ∃ c : SolvedCoverage.Chain r, c.value r=2^(2^n)-1 ∧ r ≤ n+excess

def ascend (next : Nat → Nat) : Nat → Nat
  | 0 => next 0
  | i+1 => next (ascend next i)

theorem eventual_chain_gap (C : Nat) :
    ∃ threshold, ∀ n, threshold ≤ n → ∀ r, ∀ c : SolvedCoverage.Chain r,
      c.value r=2^(2^n)-1 → n+C < r := by
  apply Classical.byContradiction
  intro absent
  have later : ∀ K, ∃ n, K<n ∧ ShortChain n C := by
    intro K
    apply Classical.byContradiction
    intro noneLater
    apply absent
    refine ⟨K+1,?_⟩
    intro n hn r c endpoint
    have notShort : ¬ r ≤ n+C := by
      intro short
      exact noneLater ⟨n,by omega,r,c,endpoint,short⟩
    omega
  let next := fun K => Classical.choose (later K)
  have nextSpec (K : Nat) : K<next K ∧ ShortChain (next K) C := Classical.choose_spec (later K)
  let index := ascend next
  have positive (i : Nat) : 1 ≤ index i := by
    cases i with
    | zero => exact (nextSpec 0).1
    | succ i =>
      have h := (nextSpec (ascend next i)).1
      change 1 ≤ next (ascend next i)
      omega
  have adjacent (i : Nat) : index i<index (i+1) := (nextSpec (index i)).1
  have rising : ∀ i j, i<j → index i<index j := SolvedControls.rising adjacent
  have present (i : Nat) : ShortChain (index i) C := by
    cases i with
    | zero => exact (nextSpec 0).2
    | succ i => exact (nextSpec (ascend next i)).2
  let lengths := fun i => Classical.choose (present i)
  let family : ∀ i, SolvedCoverage.Chain (lengths i) := fun i =>
    Classical.choose (Classical.choose_spec (present i))
  have specification (i : Nat) := Classical.choose_spec (Classical.choose_spec (present i))
  exact short_chain_sequence_impossible index lengths family C positive rising
    (fun i => (specification i).1) (fun i => (specification i).2)

end SolvedBounded
