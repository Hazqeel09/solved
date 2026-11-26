import AMNormalization

namespace SolvedSeparation
open SolvedNormalization

inductive Operation
  | add
  | subtract
  | multiply

def applyOperation : Operation → Int → Int → Int
  | .add, a, b => a+b
  | .subtract, a, b => a-b
  | .multiply, a, b => a*b

-- The signed model permits arbitrary integer intermediate values.
structure SignedProgram (length : Nat) where
  value : Nat → Int
  left : Nat → Nat
  right : Nat → Nat
  operation : Nat → Operation
  initial : value 0=1
  valid : ∀ i, 0<i → i≤length → left i<i ∧ right i<i ∧
    value i=applyOperation (operation i) (value (left i)) (value (right i))

def additiveProgram (length : Nat) : Program length where
  value i := i+1
  left i := i-1
  right := fun _ => 0
  isMul := fun _ => false
  initial := rfl
  valid := by
    intro i positive _bound
    simp only [Bool.false_eq_true,if_false]
    exact ⟨by omega,by omega,by omega⟩

def embed {r : Nat} (p : Program r) : SignedProgram r where
  value i := (p.value i : Int)
  left := p.left
  right := p.right
  operation i := if p.isMul i then .multiply else .add
  initial := by
    change (p.value 0 : Int)=1
    rw [p.initial]
    rfl
  valid := by
    intro i positive bound
    obtain ⟨hl,hr,eq⟩ := p.valid i positive bound
    refine ⟨hl,hr,?_⟩
    cases flag : p.isMul i
    · simp only [flag,Bool.false_eq_true,if_false] at eq
      simp only [flag,Bool.false_eq_true,if_false,applyOperation]
      exact congrArg Int.ofNat eq
    · simp only [flag,if_true] at eq
      simp only [flag,if_true,applyOperation]
      exact congrArg Int.ofNat eq

def append {r : Nat} (p : SignedProgram r) (op : Operation) (a b : Nat)
    (ha : a≤r) (hb : b≤r) : SignedProgram (r+1) where
  value i := if i=r+1 then applyOperation op (p.value a) (p.value b) else p.value i
  left i := if i=r+1 then a else p.left i
  right i := if i=r+1 then b else p.right i
  operation i := if i=r+1 then op else p.operation i
  initial := by simp only [show ¬0=r+1 by omega,if_false,p.initial]
  valid := by
    intro i positive bound
    by_cases newest : i=r+1
    · subst i
      simp only [if_pos rfl,if_true,show ¬a=r+1 by omega,show ¬b=r+1 by omega,if_false]
      exact ⟨by omega,by omega,True.intro⟩
    · obtain ⟨hl,hr,eq⟩ := p.valid i positive (by omega)
      simp only [if_neg newest,show ¬p.left i=r+1 by omega,show ¬p.right i=r+1 by omega,if_false]
      exact ⟨hl,hr,eq⟩

theorem append_head {r : Nat} (p : SignedProgram r) (op : Operation) (a b : Nat)
    (ha : a≤r) (hb : b≤r) :
    (append p op a b ha hb).value (r+1)=applyOperation op (p.value a) (p.value b) := by
  change (if r+1=r+1 then _ else _)=_
  rw [if_pos rfl]

def towerProgram : (n : Nat) → SignedProgram (n+1)
  | 0 => embed (additiveProgram 1)
  | n+1 => append (towerProgram n) .multiply (n+1) (n+1) (Nat.le_refl _) (Nat.le_refl _)

theorem towerProgram_head (n : Nat) :
    (towerProgram n).value (n+1)=(2^(2^n) : Nat) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (append (towerProgram n) .multiply (n+1) (n+1) _ _).value ((n+1)+1)=_
    rw [append_head]
    simp only [applyOperation,ih,← Int.ofNat_mul,← SolvedGrowth.tower_step]

def mersenneProgram (n : Nat) : SignedProgram (n+2) :=
  append (towerProgram n) .subtract (n+1) 0 (Nat.le_refl _) (Nat.zero_le _)

theorem mersenneProgram_head (n : Nat) :
    (mersenneProgram n).value (n+2)=(2^(2^n)-1 : Nat) := by
  change (append (towerProgram n) .subtract (n+1) 0 _ _).value ((n+1)+1)=_
  rw [append_head]
  simp only [applyOperation,towerProgram_head,(towerProgram n).initial]
  have large := SolvedGrowth.tower_large n
  exact (Int.ofNat_sub (show 1≤2^(2^n) by omega)).symm

def MinimumAM (target cost : Nat) : Prop :=
  (∃ p : Program cost, p.value cost=target) ∧
  ∀ r, ∀ p : Program r, p.value r=target → cost≤r

def MinimumSLP (target cost : Nat) : Prop :=
  (∃ p : SignedProgram cost, p.value cost=(target : Int)) ∧
  ∀ r, ∀ p : SignedProgram r, p.value r=(target : Int) → cost≤r

theorem least_cost (P : Nat → Prop) (present : ∃ r, P r) :
    ∃ cost, P cost ∧ ∀ r, P r → cost≤r := by
  obtain ⟨r,existsProgram⟩ := present
  have descend : ∀ r, P r → ∃ cost, P cost ∧ ∀ s, P s → cost≤s := by
    intro r
    induction r using Nat.strongInductionOn with
    | ind r ih =>
      intro current
      by_cases earlier : ∃ s, s<r ∧ P s
      · obtain ⟨s,smaller,available⟩ := earlier
        exact ih s smaller available
      · refine ⟨r,current,?_⟩
        intro s available
        by_cases smaller : s<r
        · exact False.elim (earlier ⟨s,smaller,available⟩)
        · omega
  exact descend r existsProgram

theorem minima_exist (target : Nat) (positive : 1≤target) :
    (∃ a, MinimumAM target a) ∧ (∃ b, MinimumSLP target b) := by
  have witness : ∃ r, ∃ p : Program r, p.value r=target := by
    refine ⟨target-1,additiveProgram (target-1),?_⟩
    change target-1+1=target
    omega
  have signedWitness : ∃ r, ∃ p : SignedProgram r, p.value r=(target : Int) := by
    obtain ⟨r,p,eq⟩ := witness
    exact ⟨r,embed p,congrArg Int.ofNat eq⟩
  obtain ⟨a,program,minimal⟩ := least_cost (fun r => ∃ p : Program r, p.value r=target) witness
  obtain ⟨b,signed,signedMinimal⟩ := least_cost
    (fun r => ∃ p : SignedProgram r, p.value r=(target : Int)) signedWitness
  exact ⟨⟨a,program,fun r p eq => minimal r ⟨p,eq⟩⟩,
    ⟨b,signed,fun r p eq => signedMinimal r ⟨p,eq⟩⟩⟩

theorem minima_unique {target a a' b b' : Nat}
    (am : MinimumAM target a) (am' : MinimumAM target a')
    (slp : MinimumSLP target b) (slp' : MinimumSLP target b') : a=a' ∧ b=b' := by
  obtain ⟨p,hp⟩ := am.1
  obtain ⟨p',hp'⟩ := am'.1
  obtain ⟨s,hs⟩ := slp.1
  obtain ⟨s',hs'⟩ := slp'.1
  have aBound := am.2 a' p' hp'
  have aBound' := am'.2 a p hp
  have bBound := slp.2 b' s' hs'
  have bBound' := slp'.2 b s hs
  omega

theorem eventual_additive_gap (C : Nat) :
    ∃ threshold, ∀ n, threshold≤n → ∀ a b,
      MinimumAM (2^(2^n)-1) a → MinimumSLP (2^(2^n)-1) b → b+C<a := by
  obtain ⟨threshold,lower⟩ := eventual_program_gap (C+2)
  refine ⟨threshold,?_⟩
  intro n above a b am slp
  obtain ⟨p,endpoint⟩ := am.1
  have amCost := lower n above a p endpoint
  have signedCost := slp.2 (n+2) (mersenneProgram n) (mersenneProgram_head n)
  omega

theorem unbounded_additive_advantage (C : Nat) :
    ∃ threshold, ∀ n, threshold≤n →
      ∃ a b, MinimumAM (2^(2^n)-1) a ∧ MinimumSLP (2^(2^n)-1) b ∧ b+C<a := by
  obtain ⟨threshold,gap⟩ := eventual_additive_gap C
  refine ⟨threshold,?_⟩
  intro n above
  have positive : 1≤2^(2^n)-1 := by have h := SolvedGrowth.tower_large n; omega
  obtain ⟨⟨a,am⟩,⟨b,slp⟩⟩ := minima_exist (2^(2^n)-1) positive
  exact ⟨a,b,am,slp,gap n above a b am slp⟩

end SolvedSeparation
