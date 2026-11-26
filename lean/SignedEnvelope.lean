import Lean

namespace SolvedSigned

inductive Write (a b : Nat) : Nat → Prop
  | add : Write a b (a+b)
  | mul : Write a b (a*b)
  | sub : Write a b (a-b)
  | div : Write a b (a/b)

-- The bounds even allow truncated subtraction and division, which enlarge
-- the positive exact machine. The certificate concerns its upper envelope.
theorem deviation {h j a b n : Nat}
    (hj : 2 ≤ j) (aj : a = h ∨ a ≤ j) (bj : b = h ∨ b ≤ j)
    (ah : a ≤ h) (bh : b ≤ h) (op : Write a b n) (diff : n ≠ h*h) :
    n ≤ h*j := by
  have one : 1 ≤ j := by omega
  have below : h ≤ h*j := by simpa using Nat.mul_le_mul_left h one
  cases op with
  | add =>
    calc a+b ≤ h+h := Nat.add_le_add ah bh
         _ = h*2 := by omega
         _ ≤ h*j := Nat.mul_le_mul_left h hj
  | mul =>
    rcases aj with rfl | small
    · rcases bj with rfl | small
      · exact False.elim (diff rfl)
      · exact Nat.mul_le_mul_left _ small
    · calc a*b ≤ j*h := Nat.mul_le_mul small bh
           _ = h*j := Nat.mul_comm _ _
  | sub => exact Nat.le_trans (Nat.sub_le _ _) (Nat.le_trans ah below)
  | div => exact Nat.le_trans (Nat.div_le_self _ _) (Nat.le_trans ah below)

def squares : Nat → Nat → Nat
  | 0, h => h
  | k+1, h => squares k h * squares k h

theorem monotone {x y : Nat} (h : x ≤ y) (k : Nat) : squares k x ≤ squares k y := by
  induction k with
  | zero => exact h
  | succ k ih => exact Nat.mul_le_mul ih ih

-- r counts growth writes and t counts all writes, including flat steps.
inductive Peaks (h : Nat) : Nat → Nat → Nat → Prop
  | start : Peaks h 0 0 h
  | flat {t r m} : Peaks h t r m → Peaks h (t+1) r m
  | rise {t r m z} : Peaks h t r m → m < z → z ≤ m*m → Peaks h (t+1) (r+1) z

theorem records_bound {h t r m : Nat} (p : Peaks h t r m) : m ≤ squares r h := by
  induction p with
  | start => exact Nat.le_refl _
  | flat _ ih => exact ih
  | rise _ _ bound ih => exact Nat.le_trans bound (Nat.mul_le_mul ih ih)

#print axioms deviation
#print axioms records_bound
end SolvedSigned
