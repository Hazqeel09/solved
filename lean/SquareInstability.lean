import Lean
import Compression
import FiniteLists

namespace SolvedInstability

-- Histories are newest first. Each next value strictly exceeds the head.
def unique : List Nat → List Nat
  | [] => []
  | a::as => if as.elem a then unique as else a::unique as

theorem mem_unique (v : Nat) (xs : List Nat) : v ∈ unique xs ↔ v ∈ xs := by
  induction xs with
  | nil => simp [unique]
  | cons a xs ih =>
    by_cases ha : xs.elem a = true
    · have ham : a ∈ xs := List.mem_of_elem_eq_true ha
      simp only [unique, ha, if_true, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro h; cases h with
        | inl h => subst v; exact ham
        | inr h => exact h
    · simp only [unique, ha, if_false, List.mem_cons, ih]

theorem mem_append {α : Type} (v : α) (xs ys : List α) :
    v ∈ xs++ys ↔ v ∈ xs ∨ v ∈ ys := SolvedLists.mem_append v xs ys

theorem mem_bind {α β : Type} (v : β) (xs : List α) (f : α → List β) :
    v ∈ xs.bind f ↔ ∃ a, a ∈ xs ∧ v ∈ f a := SolvedLists.mem_bind v xs f

def options (target : Nat) (xs : List Nat) : List Nat :=
  unique ((xs.bind fun a => xs.bind fun b => [a+b,a*b]).filter
    fun v => (xs.headD 0) < v && v ≤ target)

def Recipe (v : Nat) (xs : List Nat) : Prop :=
  ∃ a, a ∈ xs ∧ ∃ b, b ∈ xs ∧ (v=a+b ∨ v=a*b)

theorem mem_options (target v : Nat) (xs : List Nat) :
    v ∈ options target xs ↔ Recipe v xs ∧ (xs.headD 0) < v ∧ v ≤ target := by
  simp only [options, mem_unique, List.mem_filter, mem_bind, List.mem_cons,
    List.not_mem_nil, or_false, Bool.and_eq_true, decide_eq_true_eq, Recipe]

inductive Reach (target : Nat) : Nat → List Nat → Prop
  | done (xs : List Nat) (eq : (xs.headD 0) = target) : Reach target 0 xs
  | step {k : Nat} {xs : List Nat} (v : Nat) (r : Recipe v xs)
      (increases : (xs.headD 0) < v) (rest : Reach target k (v::xs)) :
      Reach target (k+1) xs

theorem head_le_target {target k : Nat} {xs : List Nat} (h : Reach target k xs) :
    (xs.headD 0) ≤ target := by
  induction h with
  | done xs eq => omega
  | step v _ increases _ ih =>
    simp only [List.headD] at ih
    omega

def HeadBound (xs : List Nat) : Prop := ∀ a, a ∈ xs → a ≤ (xs.headD 0)

theorem cons_bound {xs : List Nat} {v : Nat} (h : HeadBound xs)
    (rises : (xs.headD 0) < v) : HeadBound (v::xs) := by
  intro a ha
  simp only [List.mem_cons] at ha
  simp only [List.headD]
  cases ha with
  | inl eq => omega
  | inr mem => exact Nat.le_trans (h a mem) (Nat.le_of_lt rises)

def peak (x : Nat) : Nat := max (x+x) (x*x)

theorem peak_mono {x y : Nat} (h : x ≤ y) : peak x ≤ peak y := by
  have mul := Nat.mul_le_mul h h
  unfold peak
  omega

theorem le_peak (x : Nat) : x ≤ peak x := by
  unfold peak
  omega

def growth : Nat → Nat → Nat
  | 0, x => x
  | n+1, x => growth n (peak x)

theorem growth_mono (n : Nat) {x y : Nat} (h : x ≤ y) : growth n x ≤ growth n y := by
  induction n generalizing x y with
  | zero => exact h
  | succ _ ih => exact ih (peak_mono h)

theorem growth_steps {n m x : Nat} (h : n ≤ m) : growth n x ≤ growth m x := by
  induction m with
  | zero =>
    have e : n=0 := by omega
    subst n
    exact Nat.le_refl _
  | succ m ih =>
    by_cases eq : n=m+1
    · subst n; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (growth_mono m (le_peak x))

theorem recipe_bound {xs : List Nat} {v : Nat} (h : HeadBound xs)
    (r : Recipe v xs) : v ≤ peak (xs.headD 0) := by
  obtain ⟨a,ha,b,hb,op⟩ := r
  cases op with
  | inl eq =>
    have bound := Nat.add_le_add (h a ha) (h b hb)
    unfold peak
    omega
  | inr eq =>
    have bound := Nat.mul_le_mul (h a ha) (h b hb)
    unfold peak
    omega

theorem reach_bound {target k : Nat} {xs : List Nat} (h : Reach target k xs)
    (head : HeadBound xs) : target ≤ growth k (xs.headD 0) := by
  induction h with
  | done xs eq => simp only [growth]; omega
  | step v rule rises _ ih =>
    have bound := ih (cons_bound head rises)
    exact Nat.le_trans bound (growth_mono _ (recipe_bound head rule))

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def oneStep (target : Nat) (xs : List Nat) : Bool :=
  xs.any fun a => xs.any fun b => target == a+b || target == a*b

theorem oneStep_complete {target : Nat} {xs : List Nat} (r : Recipe target xs) :
    oneStep target xs = true := by
  obtain ⟨a,ha,b,hb,op⟩ := r
  apply List.any_eq_true.mpr
  refine ⟨a,ha,List.any_eq_true.mpr ⟨b,hb,?_⟩⟩
  simp only [Bool.or_eq_true, beq_iff_eq]
  exact op

def search (target : Nat) : Nat → List Nat → Bool
  | 0, xs => (xs.headD 0) == target
  | fuel+1, xs => if growth (fuel+1) (xs.headD 0) < target then false else
      (xs.headD 0) == target || if fuel=0 then oneStep target xs else
        (options target xs).any (fun v => search target fuel (v::xs))

theorem search_complete {target length : Nat} {xs : List Nat}
    (h : Reach target length xs) (head : HeadBound xs)
    (budget : Nat) (enough : length ≤ budget) :
    search target budget xs = true := by
  have bound : target ≤ growth budget (xs.headD 0) :=
    Nat.le_trans (reach_bound h head) (growth_steps enough)
  induction h generalizing budget with
  | done xs eq =>
    cases budget with
    | zero => simp [search,eq]
    | succ budget =>
      have guard : ¬ growth (budget+1) (xs.headD 0) < target := by omega
      rw [search,if_neg guard]
      simp [eq]
  | @step k xs v rule rises rest ih =>
    cases budget with
    | zero => omega
    | succ budget =>
      have guard : ¬ growth (budget+1) (xs.headD 0) < target := by omega
      rw [search,if_neg guard]
      simp only [Bool.or_eq_true]
      apply Or.inr
      by_cases last : budget=0
      · have zero : k=0 := by omega
        subst k
        cases rest with
        | done vs eq =>
          have value : v=target := eq
          rw [if_pos last]
          exact oneStep_complete (by simpa only [value] using rule)
      · rw [if_neg last]
        have nextHead := cons_bound head rises
        have nextBound := Nat.le_trans (reach_bound rest nextHead) (growth_steps (show k ≤ budget by omega))
        have tail := ih nextHead budget (by omega) nextBound
        have cap : v ≤ target := head_le_target rest
        have mem := (mem_options target v xs).mpr ⟨rule,rises,cap⟩
        exact List.any_eq_true.mpr ⟨v,mem,tail⟩

-- Kernel evaluation, without native_decide or an additional trusted oracle.
theorem no_seven_for_267 : search 267 7 [1] = false := by decide

theorem lower_267 {k : Nat} (h : Reach 267 k [1]) : 8 ≤ k := by
  apply Classical.byContradiction
  intro small
  have head : HeadBound [1] := by intro a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at ha; subst a; exact Nat.le_refl _
  have good := search_complete h head 7 (by omega)
  rw [no_seven_for_267] at good
  contradiction



-- The second exclusion is independent of the first; it certifies the exact
-- squared cost, rather than only the upper bound needed for instability.
theorem no_seven_for_square : search 71289 7 [1] = false := by decide

theorem lower_square {k : Nat} (h : Reach 71289 k [1]) : 8 ≤ k := by
  apply Classical.byContradiction
  intro small
  have head : HeadBound [1] := by
    intro a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
    subst a
    exact Nat.le_refl _
  have good := search_complete h head 7 (by omega)
  rw [no_seven_for_square] at good
  contradiction

theorem upper_267 : Reach 267 8 [1] := by
  apply Reach.step 2 (by exact ⟨1,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 4 (by exact ⟨2,by decide,2,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 16 (by exact ⟨4,by decide,4,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 256 (by exact ⟨16,by decide,16,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 260 (by exact ⟨256,by decide,4,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 264 (by exact ⟨260,by decide,4,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 266 (by exact ⟨264,by decide,2,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 267 (by exact ⟨266,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  exact Reach.done _ rfl

theorem upper_square : Reach 71289 8 [1] := by
  apply Reach.step 2 (by exact ⟨1,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 4 (by exact ⟨2,by decide,2,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 8 (by exact ⟨4,by decide,4,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 9 (by exact ⟨8,by decide,1,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 81 (by exact ⟨9,by decide,9,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 89 (by exact ⟨81,by decide,8,by decide,Or.inl rfl⟩) (by decide)
  apply Reach.step 7921 (by exact ⟨89,by decide,89,by decide,Or.inr rfl⟩) (by decide)
  apply Reach.step 71289 (by exact ⟨7921,by decide,9,by decide,Or.inr rfl⟩) (by decide)
  exact Reach.done _ rfl

def Minimum (target cost : Nat) : Prop :=
  Reach target cost [1] ∧ ∀ k, Reach target k [1] → cost ≤ k

theorem exact_pair : Minimum 267 8 ∧ Minimum (267*267) 8 := by
  exact ⟨⟨upper_267,fun _ h => lower_267 h⟩,⟨upper_square,fun _ h => lower_square h⟩⟩

theorem square_instability :
    ∃ n a b : Nat, 2 ≤ n ∧ Minimum n a ∧ Minimum (n*n) b ∧ b < a+1 := by
  exact ⟨267,8,8,by decide,exact_pair.1,exact_pair.2,by decide⟩



theorem no_universal_increment :
    ¬ (∀ n cost, 2 ≤ n → Minimum n cost → Minimum (n*n) (cost+1)) := by
  intro claim
  have wrong := claim 267 8 (by decide) exact_pair.1
  have impossible := wrong.2 8 upper_square
  omega

theorem square_extension {target k : Nat} {xs : List Nat}
    (h : Reach target k xs) (large : 2 ≤ target) :
    Reach (target*target) (k+1) xs := by
  induction h with
  | done xs eq =>
    cases xs with
    | nil => simp only [List.headD] at eq; omega
    | cons a xs =>
      have same : a=target := eq
      subst a
      have growth : target < target*target := by
        have two := Nat.mul_le_mul_left target large
        omega
      refine Reach.step (xs := target::xs) (target*target) ?_ ?_ ?_
      · exact ⟨target,by simp,target,by simp,Or.inr rfl⟩
      · exact growth
      · exact Reach.done _ rfl
  | step v rule rises _ ih => exact Reach.step v rule rises ih

theorem iterSq_large (k : Nat) : 2 ≤ SolvedCompression.iterSq k 71289 := by
  induction k with
  | zero => decide
  | succ k ih =>
    simp only [SolvedCompression.iterSq]
    have mul := Nat.mul_le_mul ih ih
    omega

theorem upper_ray (k : Nat) :
    Reach (SolvedCompression.iterSq k 71289) (8+k) [1] := by
  induction k with
  | zero => exact upper_square
  | succ k ih =>
    exact square_extension ih (iterSq_large k)

theorem cheaper_power_family (k : Nat) :
    Reach (SolvedCompression.iterSq (k+1) 267) (8+k) [1] ∧ 8+k < 8+(k+1) := by
  have fromSquare := upper_ray k
  have identity : SolvedCompression.iterSq (k+1) 267 =
      SolvedCompression.iterSq k 71289 := by
    rw [Nat.add_comm k 1,SolvedCompression.iterSq_add]
    rfl
  rw [identity]
  exact ⟨fromSquare,by omega⟩

end SolvedInstability
