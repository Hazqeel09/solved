import TwoSmallBlocks
import ControlInflation

namespace SolvedRootBlocks
open SolvedCompression

theorem square_gap {x w : Nat} (positive : 0 < w) (small : w ≤ 2*x) :
    x*x < x*x+w ∧ x*x+w < (x+1)*(x+1) := by
  simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

theorem between_not_square {x n : Nat} (lower : x*x<n) (upper : n<(x+1)*(x+1))
    (root : Nat) : n ≠ root*root := by
  intro equal
  by_cases small : root ≤ x
  · have bound := Nat.mul_le_mul small small
    omega
  · have bound := Nat.mul_le_mul (show x+1≤root by omega) (show x+1≤root by omega)
    omega

theorem proper_additions_not_square {x u v : Nat}
    (positive : 0<u+v) (left : u≤x) (right : v≤x) (root : Nat) :
    x*x+(u+v) ≠ root*root := by
  have gap := square_gap positive (show u+v≤2*x by omega)
  exact between_not_square gap.1 gap.2 root

theorem product_roots (x y : Nat) :
    (x*x)*(y*y)=(x*y)*(x*y) := by ac_rfl

theorem halved_run_product (k x y : Nat) :
    iterSq (k+1) x * (y*y) = (iterSq k x*y)*(iterSq k x*y) := by
  simp only [iterSq]
  ac_rfl

theorem halved_first_product (k x y : Nat) :
    iterSq k (x*x)*(y*y) = (iterSq k x*y)*(iterSq k x*y) := by
  rw [iterSq_mul]
  ac_rfl

-- An elementary factor argument used by the square tests in the manuscript.
theorem odd_factor_power_two (k a b : Nat) (odd : a%2=1) (product : a*b=2^k) :
    a=1 := by
  induction k generalizing b with
  | zero =>
    have positive : 0<b := by
      by_cases zero : b=0
      · simp only [zero,Nat.mul_zero,Nat.pow_zero] at product
      · omega
    have bound := Nat.le_mul_of_pos_right a positive
    simp only [Nat.pow_zero] at product
    omega
  | succ k ih =>
    have parity := congrArg (fun n => n%2) product
    simp only [Nat.mul_mod,odd,Nat.one_mul,Nat.mod_mod,Nat.pow_succ] at parity
    have even : b%2=0 := by
      rw [Nat.mul_mod] at parity
      simp at parity
      exact parity
    have decomposition : b=2*(b/2) := by omega
    have shortened : a*(b/2)=2^k := by
      apply Nat.mul_left_cancel (by decide : 0<2)
      calc
        2*(a*(b/2)) = a*(2*(b/2)) := by ac_rfl
        _ = a*b := by rw [← decomposition]
        _ = 2^k*2 := by simpa only [Nat.pow_succ] using product
        _ = 2*(2^k) := by ac_rfl
    exact ih (b/2) shortened

theorem adjacent_power_two_factors (k u : Nat) (positive : 0<u)
    (product : u*(u+2)=2^k) : u=2 := by
  have even : u%2=0 := by
    rcases Nat.mod_two_eq_zero_or_one u with even | odd
    · exact even
    · have one := odd_factor_power_two k u (u+2) odd product
      have other := odd_factor_power_two k (u+2) u (by simp [one])
        (by simpa only [Nat.mul_comm] using product)
      omega
  have decomposition : u=2*(u/2) := by have := Nat.mod_add_div u 2; omega
  cases k with
  | zero =>
    have bound := Nat.le_mul_of_pos_right u (show 0<u+2 by omega)
    simp only [Nat.pow_zero] at product
    omega
  | succ k =>
    have first : (u/2)*(u+2)=2^k := by
      apply Nat.mul_left_cancel (by decide : 0<2)
      calc
        2*((u/2)*(u+2)) = (2*(u/2))*(u+2) := by ac_rfl
        _ = u*(u+2) := by rw [← decomposition]
        _ = 2^k*2 := by simpa only [Nat.pow_succ] using product
        _ = 2*(2^k) := by ac_rfl
    have second : (u/2+1)*u=2^k := by
      have identity : (u/2+1)*u=(u/2)*(u+2) := by
        simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul]
        have twice : u/2*2=u := by omega
        rw [twice]
      rw [identity]; exact first
    rcases Nat.mod_two_eq_zero_or_one (u/2) with halfEven | halfOdd
    · have odd : (u/2+1)%2=1 := by rw [Nat.add_mod,halfEven]
      have one := odd_factor_power_two k (u/2+1) u odd second
      omega
    · have one := odd_factor_power_two k (u/2) (u+2) halfOdd first
      omega

theorem square_one_plus_power_two {root k : Nat} (square : root*root=2^k+1) :
    root=3 ∧ k=3 := by
  have positive : 1<root := by
    have power := Nat.two_pow_pos k
    by_cases small : root≤1
    · have bound := Nat.mul_le_mul small small
      omega
    · omega
  have decomposition : root=(root-1)+1 := by omega
  have factors : (root-1)*(root-1+2)=2^k := by
    rw [decomposition] at square
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one] at square ⊢
    omega
  have two := adjacent_power_two_factors k (root-1) (by omega) factors
  have r : root=3 := by omega
  have eq : 2^k=2^3 := by rw [r] at square; omega
  have le := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq eq)
  have ge := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (Nat.le_of_eq eq.symm)
  exact ⟨r,by omega⟩

theorem exchanged_square (u v : Nat) (square : u=v*v) :
    ((u*u)*u+u*u)*((u*u)*u+u*u)*((u*u)*u) =
      ((u*u+u)*((u*u)*v))*((u*u+u)*((u*u)*v)) := by
  have factor : (u*u)*u+u*u = u*(u*u+u) := by
    simp only [Nat.mul_add]
    ac_rfl
  rw [factor,square]
  ac_rfl

def exchangeSource : List SolvedMarked.Instr :=
  [.mul 0 1,.add 0 1,.mul 0 0,.mul 0 2]

def exchangeRoot : List SolvedMarked.Instr :=
  [.add 0 1,.mul 1 3,.mul 0 1]

theorem exchange_program (history : SolvedMarked.Hist)
    (first : history 0=history 1*history 1)
    (second : history 1=history 2*history 2) :
    SolvedMarked.eval exchangeSource history 0 =
      SolvedMarked.eval exchangeRoot history 0 * SolvedMarked.eval exchangeRoot history 0 := by
  simp only [exchangeSource,exchangeRoot,SolvedMarked.eval,SolvedMarked.evalI,SolvedMarked.push]
  rw [first]
  have identity := exchanged_square (history 1) (history 2) second
  simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using identity

theorem exchange_cost :
    SolvedInflation.cost exchangeRoot+1=SolvedInflation.cost exchangeSource := by decide

end SolvedRootBlocks
