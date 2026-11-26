import FiniteLists

namespace SolvedBasis

abbrev Point (d : Nat) := Fin d → Nat
abbrev Box (d : Nat) := Fin d → Option Nat

def Below {d : Nat} (a b : Point d) : Prop := ∀ i, a i ≤ b i

instance {d : Nat} : DecidableRel (@Below d) :=
  fun _ _ => Nat.decidableForallFin _

instance {d : Nat} : DecidableEq (Point d) :=
  fun a b => decidable_of_iff (∀ i, a i=b i) ⟨funext, congrFun⟩

def Fits {d : Nat} (p : Point d) (box : Box d) : Prop :=
  ∀ i, match box i with | none => True | some upper => p i ≤ upper

def indices : (d : Nat) → List (Fin d)
  | 0 => []
  | d+1 => 0 :: (indices d).map Fin.succ

theorem mem_indices {d : Nat} (i : Fin d) : i ∈ indices d := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    cases i using Fin.cases with
    | zero => exact List.Mem.head _
    | succ i =>
      apply List.Mem.tail
      exact List.mem_map.mpr ⟨i, ih i, rfl⟩

def total : (d : Nat) → (Fin d → Nat) → Nat
  | 0, _ => 0
  | d+1, f => f 0 + total d (fun i => f i.succ)

theorem total_mono {d : Nat} {f g : Fin d → Nat}
    (bound : ∀ i, f i ≤ g i) : total d f ≤ total d g := by
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => exact Nat.add_le_add (bound 0) (ih (fun i => bound i.succ))

theorem total_strict {d : Nat} {f g : Fin d → Nat}
    (bound : ∀ i, f i ≤ g i) (i : Fin d) (strict : f i < g i) :
    total d f < total d g := by
  induction d with
  | zero => exact Fin.elim0 i
  | succ d ih =>
    cases i using Fin.cases with
    | zero =>
      have tail := total_mono (fun i => bound i.succ)
      change f 0+_ < g 0+_
      omega
    | succ i =>
      have head := bound 0
      have tail := ih (fun i => bound i.succ) i strict
      change f 0+_ < g 0+_
      omega

def infiniteWeight : Option Nat → Nat
  | none => 1
  | some _ => 0

def finiteWeight : Option Nat → Nat
  | none => 0
  | some n => n

def rank {d : Nat} (box : Box d) :=
  (total d (fun i => infiniteWeight (box i)), total d (fun i => finiteWeight (box i)))

def cut {d : Nat} (box : Box d) (p : Point d) (axis : Fin d) : Box d :=
  fun i => if i=axis then some (p axis-1) else box i

theorem cut_subset {d : Nat} {box : Box d} {p x : Point d} (axis : Fin d)
    (point : Fits p box) (inside : Fits x (cut box p axis)) : Fits x box := by
  intro i
  by_cases same : i=axis
  · subst i
    have upper := inside axis
    simp only [cut, if_pos rfl] at upper
    have original := point axis
    cases bound : box axis with
    | none => trivial
    | some n =>
      simp only [bound] at original
      exact Nat.le_trans upper (Nat.le_trans (Nat.sub_le _ _) original)
  · simpa only [cut, if_neg same] using inside i

theorem cut_avoids {d : Nat} {box : Box d} {p x : Point d} (axis : Fin d)
    (positive : 0 < p axis) (inside : Fits x (cut box p axis)) : ¬Below p x := by
  intro covered
  have upper := inside axis
  simp only [cut, if_pos rfl] at upper
  have lower := covered axis
  omega

theorem cut_covers {d : Nat} {box : Box d} {p x : Point d}
    (inside : Fits x box) (uncovered : ¬Below p x) :
    ∃ axis, 0 < p axis ∧ Fits x (cut box p axis) := by
  have violating : ∃ i, x i < p i := by
    apply Classical.byContradiction
    intro absent
    apply uncovered
    intro i
    by_cases h : x i < p i
    · exact False.elim (absent ⟨i,h⟩)
    · omega
  obtain ⟨axis,strict⟩ := violating
  refine ⟨axis,by omega,?_⟩
  intro i
  by_cases same : i=axis
  · subst i; simp only [cut,if_pos rfl]; omega
  · simp only [cut,if_neg same]; exact inside i

theorem cut_rank {d : Nat} {box : Box d} {p : Point d} (axis : Fin d)
    (point : Fits p box) (positive : 0 < p axis) :
    Prod.Lex Nat.lt Nat.lt (rank (cut box p axis)) (rank box) := by
  cases old : box axis with
  | none =>
    apply Prod.Lex.left
    apply total_strict (i := axis)
    · intro i
      by_cases same : i=axis
      · subst i; simp only [cut,if_pos rfl,old,infiniteWeight]; omega
      · simp only [cut,if_neg same]; exact Nat.le_refl _
    · simp only [cut,if_pos rfl,old,infiniteWeight]; decide
  | some n =>
    have sameInf : (rank (cut box p axis)).1 = (rank box).1 := by
      apply congrArg (total d)
      funext i
      by_cases same : i=axis
      · subst i; simp only [cut,if_pos rfl,old,infiniteWeight]
      · simp only [cut,if_neg same]
    have smaller : (rank (cut box p axis)).2 < (rank box).2 := by
      apply total_strict (i := axis)
      · intro i
        by_cases same : i=axis
        · subst i
          have upper := point axis
          simp only [old] at upper
          simp only [cut,if_pos rfl,old,finiteWeight]
          omega
        · simp only [cut,if_neg same]; exact Nat.le_refl _
      · have upper := point axis
        simp only [old] at upper
        simp only [cut,if_pos rfl,old,finiteWeight]
        omega
    exact (Prod.lex_def _ _).mpr (Or.inr ⟨sameInf,smaller⟩)

structure Oracle {d : Nat} (U : Point d → Prop) where
  query : Box d → Option (Point d)
  sound : ∀ box p, query box = some p → U p ∧ Fits p box
  empty : ∀ box, query box = none → ∀ p, Fits p box → ¬U p

def explore {d : Nat} {U : Point d → Prop} (oracle : Oracle U) (box : Box d) :
    List (Point d) :=
  match _answer : oracle.query box with
  | none => []
  | some p => p :: (indices d).bind (fun i =>
      if _positive : 0 < p i then explore oracle (cut box p i) else [])
termination_by rank box
decreasing_by
  exact cut_rank i (oracle.sound box p _answer).2 _positive

def Covered {d : Nat} (basis : List (Point d)) (x : Point d) : Prop :=
  ∃ p, p ∈ basis ∧ Below p x

theorem below_refl {d : Nat} (p : Point d) : Below p p := fun _ => Nat.le_refl _

theorem below_trans {d : Nat} {p q r : Point d} (a : Below p q) (b : Below q r) :
    Below p r := fun i => Nat.le_trans (a i) (b i)

theorem fits_downward {d : Nat} {p q : Point d} {box : Box d}
    (below : Below p q) (fits : Fits q box) : Fits p box := by
  intro i
  have bound := fits i
  cases h : box i with
  | none => trivial
  | some upper => exact Nat.le_trans (below i) (by simpa only [h] using bound)

theorem search_spec {d : Nat} {U : Point d → Prop} (oracle : Oracle U) (box : Box d) :
    (∀ p, p ∈ explore oracle box → U p ∧ Fits p box) ∧
    (∀ x, U x → Fits x box → Covered (explore oracle box) x) := by
  let wf : WellFounded (fun (new old : Box d) =>
      Prod.Lex Nat.lt Nat.lt (rank new) (rank old)) :=
    InvImage.wf rank (Prod.lex Nat.lt_wfRel Nat.lt_wfRel).wf
  apply wf.induction box
  intro box ih
  cases answer : oracle.query box with
  | none =>
    have result : explore oracle box = [] := by rw [explore,answer]
    rw [result]
    constructor
    · intro p member; cases member
    · intro x hit fits; exact False.elim (oracle.empty box answer x fits hit)
  | some p =>
    have good := oracle.sound box p answer
    let branches := fun i => if 0 < p i then explore oracle (cut box p i) else []
    have result : explore oracle box = p::(indices d).bind branches := by rw [explore,answer]; rfl
    rw [result]
    constructor
    · intro q member
      rcases List.mem_cons.mp member with same | rest
      · exact same ▸ good
      · obtain ⟨axis,_,inside⟩ := (SolvedLists.mem_bind q (indices d) branches).mp rest
        by_cases positive : 0 < p axis
        · have belongs : q ∈ explore oracle (cut box p axis) := by
            simpa only [branches,if_pos positive] using inside
          have next := (ih (cut box p axis) (cut_rank axis good.2 positive)).1 q belongs
          exact ⟨next.1,cut_subset axis good.2 next.2⟩
        · simp only [branches,if_neg positive] at inside
          cases inside
    · intro x hit fits
      by_cases covered : Below p x
      · exact ⟨p,List.Mem.head _,covered⟩
      · obtain ⟨axis,positive,inside⟩ := cut_covers fits covered
        obtain ⟨q,member,below⟩ :=
          (ih (cut box p axis) (cut_rank axis good.2 positive)).2 x hit inside
        refine ⟨q,List.Mem.tail _ ?_,below⟩
        apply (SolvedLists.mem_bind q (indices d) branches).mpr
        refine ⟨axis,mem_indices axis,?_⟩
        simpa only [branches,if_pos positive] using member

def StrictBelow {d : Nat} (p q : Point d) : Prop := Below p q ∧ ¬Below q p

instance {d : Nat} : DecidableRel (@StrictBelow d) :=
  fun _ _ => inferInstanceAs (Decidable (_ ∧ ¬_))

theorem strict_total {d : Nat} {p q : Point d} (strict : StrictBelow p q) :
    total d p < total d q := by
  have differing : ∃ i, p i < q i := by
    apply Classical.byContradiction
    intro absent
    apply strict.2
    intro i
    by_cases h : p i < q i
    · exact False.elim (absent ⟨i,h⟩)
    · omega
  obtain ⟨i,lt⟩ := differing
  exact total_strict strict.1 i lt

def prune {d : Nat} (points : List (Point d)) : List (Point d) :=
  SolvedLists.unique (points.filter fun p => !(points.any fun q => decide (StrictBelow q p)))

theorem mem_prune {d : Nat} (points : List (Point d)) (p : Point d) :
    p ∈ prune points ↔ p ∈ points ∧ ¬∃ q, q ∈ points ∧ StrictBelow q p := by
  simp only [prune,SolvedLists.mem_unique,List.mem_filter,Bool.not_eq_true',
    Bool.eq_false_iff,ne_eq,List.any_eq_true,decide_eq_true_eq]

theorem pruning_covers {d : Nat} (points : List (Point d)) (p : Point d) (member : p ∈ points) :
    Covered (prune points) p := by
  have claim : ∀ n, ∀ p : Point d, total d p=n → p ∈ points → Covered (prune points) p := by
    intro n
    apply Nat.strongInductionOn n
    intro n ih p size member
    by_cases minimal : ¬∃ q, q ∈ points ∧ StrictBelow q p
    · exact ⟨p,(mem_prune points p).mpr ⟨member,minimal⟩,below_refl p⟩
    · obtain ⟨q,inside,below⟩ := Classical.not_not.mp minimal
      obtain ⟨r,kept,order⟩ := ih (total d q) (by have := strict_total below; omega) q rfl inside
      exact ⟨r,kept,below_trans order below.1⟩
  exact claim (total d p) p rfl member

def Minimal {d : Nat} (U : Point d → Prop) (p : Point d) : Prop :=
  U p ∧ ∀ q, U q → Below q p → Below p q

def basis {d : Nat} {U : Point d → Prop} (oracle : Oracle U) (box : Box d) :=
  prune (explore oracle box)

theorem basis_spec {d : Nat} {U : Point d → Prop} (oracle : Oracle U) (box : Box d) :
    (∀ p, p ∈ basis oracle box → Minimal U p ∧ Fits p box) ∧
    (∀ x, U x → Fits x box → Covered (basis oracle box) x) := by
  have search := search_spec oracle box
  constructor
  · intro p member
    have retained := (mem_prune (explore oracle box) p).mp member
    have good := search.1 p retained.1
    refine ⟨⟨good.1,?_⟩,good.2⟩
    intro q qhit below
    obtain ⟨r,inside,rb⟩ := search.2 q qhit (fits_downward below good.2)
    have rp := below_trans rb below
    have pr : Below p r := by
      by_cases pr : Below p r
      · exact pr
      · exact False.elim (retained.2 ⟨r,inside,rp,pr⟩)
    exact below_trans pr rb
  · intro x hit fits
    obtain ⟨p,member,below⟩ := search.2 x hit fits
    obtain ⟨q,retained,order⟩ := pruning_covers (explore oracle box) p member
    exact ⟨q,retained,below_trans order below⟩

end SolvedBasis
