import Compression

/- Exact coverage facts for increasing addition-multiplication chains.
   These statements retain every operand read, including old values inside runs. -/
namespace SolvedCoverage
open SolvedCompression

structure Chain (length : Nat) where
  value : Nat → Nat
  left : Nat → Nat
  right : Nat → Nat
  isMul : Nat → Bool
  initial : value 0 = 1
  increasing : ∀ i j, i < j → j ≤ length → value i < value j
  valid : ∀ i, 0 < i → i ≤ length →
    left i < i ∧ right i < i ∧
    value i = if isMul i then value (left i) * value (right i)
      else value (left i) + value (right i)

def Square {r : Nat} (c : Chain r) (i : Nat) : Prop :=
  c.value i = c.value (i-1) * c.value (i-1)

def Marked {r : Nat} (c : Chain r) (i : Nat) : Prop :=
  i = 0 ∨ i = r ∨ (0 < i ∧ i ≤ r ∧ ¬ Square c i) ∨
  ∃ j, 0 < j ∧ j ≤ r ∧ ¬ Square c j ∧ (c.left j = i ∨ c.right j = i)

theorem monotone {r : Nat} (c : Chain r) {i j : Nat}
    (ij : i ≤ j) (jr : j ≤ r) : c.value i ≤ c.value j := by
  by_cases eq : i = j
  · subst i; exact Nat.le_refl _
  · exact Nat.le_of_lt (c.increasing i j (by omega) jr)

theorem at_least_two {r : Nat} (c : Chain r) {i : Nat}
    (pos : 0 < i) (bound : i ≤ r) : 2 ≤ c.value i := by
  have h := c.increasing 0 i pos bound
  rw [c.initial] at h
  omega

theorem sum_le_square {a b x : Nat} (ha : a ≤ x) (hb : b ≤ x)
    (hx : 2 ≤ x) : a+b ≤ x*x := by
  calc
    a+b ≤ x+x := Nat.add_le_add ha hb
    _ = 2*x := by omega
    _ ≤ x*x := Nat.mul_le_mul_right x hx

theorem first_not_square {r : Nat} (c : Chain r) (bound : 1 ≤ r) :
    ¬ Square c 1 := by
  intro h
  have lower := at_least_two c (by omega : 0 < 1) bound
  simp only [Square, Nat.sub_self, c.initial, Nat.mul_one] at h
  omega

theorem reads_head_after_square {r k : Nat} (c : Chain r)
    (positive : 0 < k) (bound : k+2 ≤ r) (sq : Square c (k+1)) :
    c.left (k+2) = k+1 ∨ c.right (k+2) = k+1 := by
  obtain ⟨hl, hr, he⟩ := c.valid (k+2) (by omega) bound
  apply Classical.byContradiction
  intro neither
  have lb : c.left (k+2) ≤ k := by omega
  have rb : c.right (k+2) ≤ k := by omega
  have leftValue := monotone c lb (by omega : k ≤ r)
  have rightValue := monotone c rb (by omega : k ≤ r)
  have large := at_least_two c positive (by omega : k ≤ r)
  have growth := c.increasing (k+1) (k+2) (by omega) bound
  have top : c.value (k+1) = c.value k * c.value k := by
    simpa only [Square, Nat.add_sub_cancel] using sq
  have product := Nat.mul_le_mul leftValue rightValue
  have addition := sum_le_square leftValue rightValue large
  cases flag : c.isMul (k+2) <;> simp only [flag, Bool.false_eq_true, if_false, if_true] at he <;> omega

theorem predecessor_marked {r i : Nat} (c : Chain r)
    (pos : 0 < i) (bound : i ≤ r) (non : ¬ Square c i) :
    Marked c (i-1) := by
  by_cases first : i=1
  · subst i; exact Or.inl rfl
  by_cases predSquare : Square c (i-1)
  · have two : i ≠ 2 := by
      intro eq
      subst i
      exact first_not_square c (by omega) predSquare
    have lower : 0 < i-2 := by omega
    have equation : i-2+2=i := by omega
    have equationPred : i-2+1=i-1 := by omega
    have read := reads_head_after_square c lower (by omega : i-2+2 ≤ r)
      (by simpa only [equationPred] using predSquare)
    rw [equation, equationPred] at read
    exact Or.inr (Or.inr (Or.inr ⟨i,pos,bound,non,read⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨by omega,by omega,predSquare⟩))

theorem unmarked_is_square {r i : Nat} (c : Chain r)
    (pos : 0 < i) (bound : i ≤ r) (unmarked : ¬ Marked c i) :
    Square c i := by
  apply Classical.byContradiction
  intro non
  exact unmarked (Or.inr (Or.inr (Or.inl ⟨pos,bound,non⟩)))

theorem nonsquare_boundary_adjacent {r a b : Nat} (c : Chain r)
    (ab : a < b) (bound : b ≤ r) (non : ¬ Square c b)
    (gap : ∀ i, a < i → i < b → ¬ Marked c i) : b = a+1 := by
  have pred := predecessor_marked c (by omega : 0 < b) bound non
  apply Classical.byContradiction
  intro notNext
  exact gap (b-1) (by omega) (by omega) pred

theorem square_run {r : Nat} (c : Chain r) (a d : Nat)
    (bound : a+d ≤ r)
    (steps : ∀ i, a < i → i ≤ a+d → Square c i) :
    c.value (a+d) = iterSq d (c.value a) := by
  induction d with
  | zero => simp only [Nat.add_zero, iterSq]
  | succ d ih =>
    have previous := ih (by omega) (fun i hi hj => steps i hi (by omega))
    have last := steps (a+d+1) (by omega) (by omega)
    have pred : a+d+1-1=a+d := by omega
    simp only [Square, pred] at last
    simp only [Nat.add_succ, iterSq]
    exact last.trans (congrArg (fun x => x*x) previous)

theorem square_boundary_run {r a b : Nat} (c : Chain r)
    (ab : a < b) (bound : b ≤ r) (sq : Square c b)
    (gap : ∀ i, a < i → i < b → ¬ Marked c i) :
    c.value b = iterSq (b-a) (c.value a) := by
  have distance : a+(b-a)=b := by omega
  have result := square_run c a (b-a) (by omega) (by
    intro i hi hj
    by_cases endpoint : i=b
    · subst i; exact sq
    · exact unmarked_is_square c (by omega) (by omega) (gap i hi (by omega)))
  simpa only [distance] using result

end SolvedCoverage
