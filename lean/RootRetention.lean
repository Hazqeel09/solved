import SquareInstability

namespace SolvedRootRetention
open SolvedInstability

-- The existing arithmetic relation, with one observable retained output.
inductive MarkedReach (target mark : Nat) : Nat → List Nat → Prop
  | done (xs : List Nat) (endpoint : xs.headD 0=target) (marked : mark∈xs) :
      MarkedReach target mark 0 xs
  | step {k : Nat} {xs : List Nat} (v : Nat) (rule : Recipe v xs)
      (rises : xs.headD 0<v) (rest : MarkedReach target mark k (v::xs)) :
      MarkedReach target mark (k+1) xs

theorem forget {target mark k : Nat} {xs : List Nat}
    (h : MarkedReach target mark k xs) : Reach target k xs := by
  induction h with
  | done xs endpoint _ => exact Reach.done xs endpoint
  | step v rule rises _ ih => exact Reach.step v rule rises ih

theorem future_mark {target mark k : Nat} {xs : List Nat}
    (h : MarkedReach target mark k xs) (absent : mark∉xs) : xs.headD 0<mark := by
  induction h with
  | done _ _ marked => exact False.elim (absent marked)
  | @step _k xs v _ rises _ ih =>
    by_cases same : mark=v
    · simpa only [same] using rises
    · have missing : mark∉v::xs := by
        intro member
        simp only [List.mem_cons] at member
        exact member.elim same absent
      have later := ih missing
      exact Nat.lt_trans rises later

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def markedSearch (target mark : Nat) (budget : Nat) (xs : List Nat) : Bool :=
  if xs.elem mark then search target budget xs else
    match budget with
    | 0 => false
    | fuel+1 => if growth (fuel+1) (xs.headD 0)<target ∨ mark≤xs.headD 0 then false else
        (options target xs).any (fun v => markedSearch target mark fuel (v::xs))

theorem marked_search_complete {target mark length : Nat} {xs : List Nat}
    (h : MarkedReach target mark length xs) (head : HeadBound xs)
    (budget : Nat) (enough : length≤budget) : markedSearch target mark budget xs=true := by
  induction h generalizing budget with
  | done xs endpoint marked =>
    have present := List.elem_eq_true_of_mem marked
    cases budget with
    | zero => simp [markedSearch,present,search,endpoint]
    | succ budget =>
      rw [markedSearch,if_pos present]
      exact search_complete (Reach.done xs endpoint) head (budget+1) enough
  | @step k xs v rule rises rest ih =>
    by_cases marked : mark∈xs
    · have present := List.elem_eq_true_of_mem marked
      cases budget with
      | zero => omega
      | succ budget =>
        rw [markedSearch,if_pos present]
        exact search_complete (Reach.step v rule rises (forget rest)) head (budget+1) enough
    · have absent : ¬ xs.elem mark=true := fun h => marked (List.mem_of_elem_eq_true h)
      cases budget with
      | zero => omega
      | succ budget =>
        have reach := forget (MarkedReach.step v rule rises rest)
        have bound := Nat.le_trans (reach_bound reach head) (growth_steps enough)
        have future := future_mark (MarkedReach.step v rule rises rest) marked
        have guard : ¬ (growth (budget+1) (xs.headD 0)<target ∨ mark≤xs.headD 0) := by omega
        rw [markedSearch,if_neg absent,if_neg guard]
        have cap := head_le_target (forget rest)
        have member := (mem_options target v xs).mpr ⟨rule,rises,cap⟩
        exact List.any_eq_true.mpr
          ⟨v,member,ih (cons_bound head rises) budget (by omega)⟩

theorem initial_head_bound : HeadBound [1] := by
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  subst a
  exact Nat.le_refl _

-- Each exclusion is a kernel reduction of a complete search.
theorem no_five_for_root : search 2000 5 [1]=false := by decide

theorem no_six_for_source : search 4000000 6 [1]=false := by decide

theorem no_six_with_mark : markedSearch 2000 10 6 [1]=false := by decide

theorem root_lower {k : Nat} (h : Reach 2000 k [1]) : 6≤k := by
  apply Classical.byContradiction
  intro smaller
  have found := search_complete h initial_head_bound 5 (by omega)
  rw [no_five_for_root] at found
  contradiction

theorem source_lower {k : Nat} (h : Reach 4000000 k [1]) : 7≤k := by
  apply Classical.byContradiction
  intro smaller
  have found := search_complete h initial_head_bound 6 (by omega)
  rw [no_six_for_source] at found
  contradiction

theorem marked_lower {k : Nat} (h : MarkedReach 2000 10 k [1]) : 7≤k := by
  apply Classical.byContradiction
  intro smaller
  have found := marked_search_complete h initial_head_bound 6 (by omega)
  rw [no_six_with_mark] at found
  contradiction

theorem root_upper : Reach 2000 6 [1] := by
  apply Reach.step 2 (by exact ⟨1,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 4 (by exact ⟨2,by decide,2,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 5 (by exact ⟨4,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 20 (by exact ⟨4,by decide,5,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 100 (by exact ⟨5,by decide,20,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 2000 (by exact ⟨20,by decide,100,by decide,Or.inr rfl⟩) (by decide)
  exact Reach.done _ rfl

theorem source_upper : MarkedReach 4000000 100 7 [1] := by
  apply MarkedReach.step 2 (by exact ⟨1,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply MarkedReach.step 4 (by exact ⟨2,by decide,2,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 5 (by exact ⟨4,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply MarkedReach.step 20 (by exact ⟨4,by decide,5,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 100 (by exact ⟨5,by decide,20,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 2000 (by exact ⟨20,by decide,100,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 4000000 (by exact ⟨2000,by decide,2000,by decide,Or.inr rfl⟩) (by decide)
  exact MarkedReach.done _ rfl (by decide)

theorem marked_upper : MarkedReach 2000 10 7 [1] := by
  apply MarkedReach.step 2 (by exact ⟨1,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply MarkedReach.step 3 (by exact ⟨1,by decide,2,by decide,Or.inl rfl⟩) (by decide)
  apply MarkedReach.step 5 (by exact ⟨2,by decide,3,by decide,Or.inl rfl⟩) (by decide)
  apply MarkedReach.step 10 (by exact ⟨2,by decide,5,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 20 (by exact ⟨2,by decide,10,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 100 (by exact ⟨10,by decide,10,by decide,Or.inr rfl⟩) (by decide)
  apply MarkedReach.step 2000 (by exact ⟨20,by decide,100,by decide,Or.inr rfl⟩) (by decide)
  exact MarkedReach.done _ rfl (by decide)

def MarkedMinimum (target mark cost : Nat) : Prop :=
  MarkedReach target mark cost [1] ∧ ∀ k, MarkedReach target mark k [1] → cost≤k

theorem exact_costs : Minimum 2000 6 ∧ Minimum 4000000 7 ∧ MarkedMinimum 2000 10 7 := by
  exact ⟨⟨root_upper,fun _ h => root_lower h⟩,
    ⟨forget source_upper,fun _ h => source_lower h⟩,
    ⟨marked_upper,fun _ h => marked_lower h⟩⟩

def InLevel (n L : Nat) : Prop := 2^(2^(L-1))≤n ∧ n<2^(2^L)

theorem source_level : InLevel 4000000 5 ∧ 7=5+2 := by
  unfold InLevel
  decide

theorem no_uniform_root_retention :
    ¬ (∀ N m R M r L : Nat, 0<L → InLevel N L → r≤L+2 →
      Minimum N r → MarkedReach N m r [1] → R*R=N → M*M=m →
      ∃ k, k<r ∧ MarkedReach R M k [1]) := by
  intro uniform
  obtain ⟨k,shorter,reachable⟩ := uniform 4000000 100 2000 10 7 5
    (by decide) source_level.1 (by decide) exact_costs.2.1 source_upper (by decide) (by decide)
  have lower := marked_lower reachable
  omega

end SolvedRootRetention
