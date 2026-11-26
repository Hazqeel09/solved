import Lean

/- Upper growth after one extra square in an otherwise fixed marked description.
   The ordinal and counting arguments are in results/am-defect-order/PROOF.md. -/
namespace SolvedMarked
abbrev Hist := Nat → Nat

def push (x : Nat) (h : Hist) : Hist
  | 0 => x
  | i+1 => h i

def iterSq : Nat → Nat → Nat
  | 0, x => x
  | k+1, x => iterSq k x * iterSq k x

def Bound (new old : Hist) : Prop := ∀ i, new i ≤ old i * old i

theorem self_le_sq (n : Nat) : n ≤ n*n := by
  cases n with
  | zero => simp
  | succ n => exact Nat.le_mul_of_pos_right _ (by omega)

theorem add_bound {a b x y : Nat} (ha : a ≤ x*x) (hb : b ≤ y*y) :
  a+b ≤ (x+y)*(x+y) := by
  calc
    a+b ≤ x*x+y*y := Nat.add_le_add ha hb
    _ ≤ (x*x + y*y) + (x*y + y*x) := Nat.le_add_right _ _
    _ = (x+y)*(x+y) := by simp only [Nat.add_mul,Nat.mul_add]; ac_rfl

theorem mul_bound {a b x y : Nat} (ha : a ≤ x*x) (hb : b ≤ y*y) :
  a*b ≤ (x*y)*(x*y) := by
  calc
    a*b ≤ (x*x)*(y*y) := Nat.mul_le_mul ha hb
    _ = (x*y)*(x*y) := by ac_rfl

theorem run_bound {a x : Nat} (ha : a ≤ x*x) (k : Nat) :
  iterSq k a ≤ iterSq k x * iterSq k x := by
  induction k with
  | zero => exact ha
  | succ k ih => exact mul_bound ih ih

theorem push_bound {a x : Nat} {new old : Hist} (hv : a ≤ x*x) (h : Bound new old) :
    Bound (push a new) (push x old) := by
  intro i; cases i with
  | zero => exact hv
  | succ i => exact h i

inductive Instr
  | add (a b : Nat)
  | mul (a b : Nat)
  | sqRun (a k : Nat)

def evalI : Instr → Hist → Hist
  | .add a b,h => push (h a + h b) h
  | .mul a b,h => push (h a * h b) h
  | .sqRun a k,h => push (iterSq k (h a)) h

theorem instruction_bound (instr : Instr) {new old : Hist} (h : Bound new old) :
    Bound (evalI instr new) (evalI instr old) := by
  cases instr with
  | add a b => exact push_bound (add_bound (h a) (h b)) h
  | mul a b => exact push_bound (mul_bound (h a) (h b)) h
  | sqRun a k => exact push_bound (run_bound (h a) k) h

def eval : List Instr → Hist → Hist
  | [],h => h
  | i::is,h => eval is (evalI i h)

theorem suffix_bound (code : List Instr) {new old : Hist} (h : Bound new old) :
    Bound (eval code new) (eval code old) := by
  induction code generalizing new old with
  | nil => exact h
  | cons i _ ih => exact ih (instruction_bound i h)

theorem one_extra_square (suffix : List Instr) (a k : Nat) (h : Hist) :
    Bound (eval suffix (evalI (.sqRun a (k+1)) h)) (eval suffix (evalI (.sqRun a k) h)) := by
  apply suffix_bound
  exact push_bound (Nat.le_refl _) (fun j => self_le_sq (h j))

#print axioms one_extra_square
end SolvedMarked
