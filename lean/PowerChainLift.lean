import ChainCoverage

namespace SolvedPowerLift
open SolvedCoverage

def AdditionOnly {r : Nat} (c : Chain r) : Prop :=
  ∀ i, 0<i → i≤r → c.isMul i=false

def liftedValues {r : Nat} (c : Chain r) : Nat → Nat
  | 0 => 1
  | i+1 => 2^(c.value i)

def liftedLeft {r : Nat} (c : Chain r) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | i+2 => c.left (i+1)+1

def liftedRight {r : Nat} (c : Chain r) : Nat → Nat
  | 0 => 0
  | 1 => 0
  | i+2 => c.right (i+1)+1

def liftedMul : Nat → Bool
  | 0 => false
  | 1 => false
  | _+2 => true

theorem values_increasing {r : Nat} (c : Chain r) {i j : Nat}
    (ordered : i<j) (bound : j≤r+1) : liftedValues c i<liftedValues c j := by
  cases j with
  | zero => omega
  | succ j =>
    cases i with
    | zero =>
      have positive := monotone c (Nat.zero_le j) (show j≤r by omega)
      rw [c.initial] at positive
      have power : 2^1≤2^(c.value j) :=
        (Nat.pow_le_pow_iff_right (by decide : 1<2)).mpr positive
      simp only [liftedValues]
      simp only [Nat.pow_one] at power
      omega
    | succ i =>
      exact (Nat.pow_lt_pow_iff_right (by decide : 1<2)).mpr
        (c.increasing i j (by omega) (by omega))

def lift {r : Nat} (c : Chain r) (addition : AdditionOnly c) : Chain (r+1) where
  value := liftedValues c
  left := liftedLeft c
  right := liftedRight c
  isMul := liftedMul
  initial := rfl
  increasing := fun _ _ h b => values_increasing c h b
  valid := by
    intro i positive bound
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => simp [liftedValues,liftedLeft,liftedRight,liftedMul,c.initial]
      | succ i =>
        obtain ⟨hl,hr,recipe⟩ := c.valid (i+1) (by omega) (by omega)
        have add := addition (i+1) (by omega) (by omega)
        simp only [add,Bool.false_eq_true,if_false] at recipe
        refine ⟨by simpa [liftedLeft] using Nat.succ_lt_succ hl,
          by simpa [liftedRight] using Nat.succ_lt_succ hr,?_⟩
        simp only [liftedValues,liftedLeft,liftedRight,liftedMul,if_true]
        rw [recipe,Nat.pow_add]

theorem lift_endpoint {r : Nat} (c : Chain r) (addition : AdditionOnly c) :
    (lift c addition).value (r+1)=2^(c.value r) := rfl

theorem lift_root {r exponent : Nat} (c : Chain r) (addition : AdditionOnly c)
    (half : c.value r+c.value r=exponent) :
    ∃ output : Chain (r+1), output.value (r+1)*output.value (r+1)=2^exponent := by
  refine ⟨lift c addition,?_⟩
  rw [lift_endpoint,← Nat.pow_add,half]

end SolvedPowerLift
