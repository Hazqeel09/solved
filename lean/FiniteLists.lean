import Lean

namespace SolvedLists

-- Shared list facts, extracted from the existing exact-chain verifier.
theorem mem_append {α : Type} (v : α) (xs ys : List α) :
    v ∈ xs++ys ↔ v ∈ xs ∨ v ∈ ys := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.append,ih,or_assoc]

theorem mem_bind {α β : Type} (v : β) (xs : List α) (f : α → List β) :
    v ∈ xs.bind f ↔ ∃ a, a ∈ xs ∧ v ∈ f a := by
  induction xs with
  | nil => simp [List.bind]
  | cons a xs ih =>
    change v ∈ f a ++ xs.bind f ↔ ∃ x, x ∈ a::xs ∧ v ∈ f x
    rw [mem_append,ih]
    simp [or_and_right,exists_or]

def unique {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a::tail => if a ∈ tail then unique tail else a::unique tail

theorem mem_unique {α : Type} [DecidableEq α] (v : α) (xs : List α) :
    v ∈ unique xs ↔ v ∈ xs := by
  induction xs with
  | nil => simp only [unique]
  | cons a tail ih =>
    by_cases inside : a ∈ tail
    · simp only [unique, if_pos inside, ih, List.mem_cons]
      constructor
      · exact Or.inr
      · intro h
        rcases h with same | remains
        · exact same ▸ inside
        · exact remains
    · simp only [unique, if_neg inside, List.mem_cons, ih]

end SolvedLists
