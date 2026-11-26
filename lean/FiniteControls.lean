import Lean

/- Finite-dimensional descending-sequence obstruction, over an arbitrary
   collection of admissible descriptions. This part needs no real-log library. -/
namespace SolvedControls

theorem suffix_min (f : Nat → Nat) (start : Nat) :
    ∃ i, start ≤ i ∧ ∀ j, start ≤ j → f i ≤ f j := by
  let Goal := ∃ i, start ≤ i ∧ ∀ j, start ≤ j → f i ≤ f j
  have via : ∀ m, ∀ i, start ≤ i → f i = m → Goal := by
    intro m
    apply Nat.strongInductionOn m
    intro m ih
    intro i hi hv
    rcases Classical.em (∃ j, start ≤ j ∧ f j < m) with bad | bad
    · obtain ⟨j,hj,hlt⟩ := bad
      exact ih (f j) hlt j hj rfl
    · refine ⟨i, hi, ?_⟩
      intro j hj
      apply Nat.le_of_not_gt
      intro hn
      exact bad ⟨j,hj,by omega⟩
  exact via (f start) start (Nat.le_refl _) rfl

noncomputable def nextPos (f : Nat → Nat) (start : Nat) : Nat :=
  Classical.choose (suffix_min f start)

theorem next_spec (f : Nat → Nat) (start : Nat) :
    start ≤ nextPos f start ∧ ∀ j, start ≤ j → f (nextPos f start) ≤ f j :=
  Classical.choose_spec (suffix_min f start)

noncomputable def places (f : Nat → Nat) : Nat → Nat
  | 0 => nextPos f 0
  | k+1 => nextPos f (places f k + 1)

theorem places_rise (f : Nat → Nat) (k : Nat) : places f k < places f (k+1) :=
  (next_spec f (places f k+1)).1

theorem places_good (f : Nat → Nat) (k j : Nat) (hj : places f k ≤ j) :
    f (places f k) ≤ f j := by
  cases k with
  | zero => exact (next_spec f 0).2 j (Nat.zero_le j)
  | succ k =>
    apply (next_spec f (places f k+1)).2
    exact Nat.le_trans (next_spec f (places f k+1)).1 hj

theorem rising {g : Nat → Nat} (h : ∀ i, g i < g (i+1)) :
    ∀ i j, i < j → g i < g j := by
  intro i j
  induction j with
  | zero => omega
  | succ j ih =>
    intro hlt
    by_cases eq : i=j
    · subst i; exact h j
    · exact Nat.lt_trans (ih (by omega)) (h j)

theorem thin (f : Nat → Nat → Nat) (k : Nat) :
    ∃ g : Nat → Nat, (∀ i j, i < j → g i < g j) ∧
        ∀ c, c < k → ∀ i j, i < j → f (g i) c ≤ f (g j) c := by
  induction k with
  | zero =>
    refine ⟨fun i=>i,fun _ _ h=>h,?_⟩
    intro c hc;omega
  | succ k ih =>
    obtain ⟨g,gi,gf⟩ := ih
    let v := fun i=>f (g i) k
    let t := places v
    have ti : ∀ i j, i<j → t i < t j := rising (places_rise v)
    refine ⟨fun i=>g (t i),fun i j h=>gi _ _ (ti _ _ h),?_⟩
    intro c hc i j hij
    by_cases eq : c=k
    · subst c
      exact places_good v i _ (Nat.le_of_lt (ti i j hij))
    · exact gf c (by omega) _ _ (ti i j hij)

theorem no_descending {β : Type} (le : β → β → Prop) (values : Nat → β)
    (coords : Nat → Nat → Nat) (dim : Nat)
    (mono : ∀ i j, (∀ c, c<dim → coords i c ≤ coords j c) → le (values i) (values j)) :
    ¬ (∀ i j, i<j → ¬ le (values i) (values j)) := by
  obtain ⟨g,gi,gf⟩ := thin coords dim
  intro bad
  exact bad _ _ (gi 0 1 (by omega)) (mono _ _ (fun c hc=>gf c hc 0 1 (by omega)))

#print axioms no_descending
end SolvedControls
