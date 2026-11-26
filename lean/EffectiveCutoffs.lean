import Lean

namespace SolvedEffective

-- The first two binomial terms give an entirely integer witness bound.
theorem first_two_terms (b k : Nat) :
    b^(k+1) + (k+1)*b^k ≤ (b+1)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have scaled := Nat.mul_le_mul_right (b+1) ih
    simp only [Nat.succ_eq_add_one, Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.mul_one,
      Nat.one_mul, Nat.mul_assoc] at scaled ⊢
    simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] at scaled ⊢
    have nonnegative := Nat.zero_le (k*b^k)
    omega

theorem integer_ratio_witness {b v s x : Nat}
    (positive : 0 < b) (gap : b < v) (nonzero : 0 < x)
    (large : b*s ≤ x) : b^x * s < v^x := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0)
  have h := first_two_terms b k
  have powers : (b+1)^(k+1) ≤ v^(k+1) := Nat.pow_le_pow_of_le_left (by omega) _
  have strict : b*s < b+(k+1) := by omega
  have pospow : 0 < b^k := Nat.pow_pos positive
  have scaled := Nat.mul_lt_mul_of_pos_left strict pospow
  calc
    b^(k+1)*s = b^k*(b*s) := by simp only [Nat.pow_succ, Nat.mul_assoc]
    _ < b^k*(b+(k+1)) := scaled
    _ = b^(k+1)+(k+1)*b^k := by
      simp only [Nat.mul_add, Nat.pow_succ, Nat.mul_comm]
    _ ≤ (b+1)^(k+1) := h
    _ ≤ v^(k+1) := powers

theorem positive_power_strict {a b : Nat} (h : a < b) (k : Nat) :
    a^(k+1) < b^(k+1) := by
  rw [Nat.pow_succ, Nat.pow_succ]
  have weak := Nat.mul_le_mul_right a (Nat.pow_le_pow_of_le_left (Nat.le_of_lt h) k)
  have strict := Nat.mul_lt_mul_of_pos_left h (Nat.pow_pos (by omega : 0 < b) : 0 < b^k)
  exact Nat.lt_of_le_of_lt weak strict

-- Apply the integer-ratio witness after collecting all lower-degree factors.
-- Profile construction itself remains a written argument in this entry.
theorem profile_upper_witness {e b v s x m : Nat}
    (positive : 0 < b) (gap : b < v) (nonzero : 0 < x)
    (large : b*s ≤ x) (upper : e ≤ (b^x*s)^(x^m)) :
    e ≤ v^(x^(m+1))-1 := by
  have strict := integer_ratio_witness positive gap nonzero large
  have exponent : 0 < x^m := Nat.pow_pos nonzero
  have power := positive_power_strict strict (x^m-1)
  have pred : x^m-1+1=x^m := by omega
  rw [pred, ← Nat.pow_mul] at power
  have product : x*x^m=x^(m+1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [product] at power
  omega

theorem profile_lower_excludes {e b v x d : Nat}
    (positive : 0 < v) (leading : v ≤ b) (lower : b^(x^d) ≤ e) :
    v^(x^d)-1 < e := by
  have bound := Nat.pow_le_pow_of_le_left leading (x^d)
  have pos : 0 < v^(x^d) := Nat.pow_pos positive
  omega

end SolvedEffective
