import Lean
namespace SolvedPositive
universe u

inductive Expr (α : Type u) (n : Nat)
  | fixed (c : α)
  | atom (i : Fin n)
  | add (left right : Expr α n)
  | mul (left right : Expr α n)

def eval {α : Type u} {n : Nat} (add mul : α → α → α) (p : Fin n → α) : Expr α n → α
  | .fixed c => c
  | .atom i => p i
  | .add x y => add (eval add mul p x) (eval add mul p y)
  | .mul x y => mul (eval add mul p x) (eval add mul p y)

theorem normalized_monotone {α : Type u} {n : Nat}
    (le : α → α → Prop) (refl : ∀ x, le x x) (add mul : α → α → α)
    (ha : ∀ {a b c d}, le a c → le b d → le (add a b) (add c d))
    (hm : ∀ {a b c d}, le a c → le b d → le (mul a b) (mul c d))
    (lo hi : Fin n → α) (h : ∀ i, le (lo i) (hi i)) (e : Expr α n) :
    le (eval add mul lo e) (eval add mul hi e) := by
  induction e with
  | fixed c => exact refl c
  | atom i => exact h i
  | add _ _ ih jh => exact ha ih jh
  | mul _ _ ih jh => exact hm ih jh

#print axioms normalized_monotone
end SolvedPositive
