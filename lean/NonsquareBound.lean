import ChainCoverage

namespace SolvedGrowth
open SolvedCoverage

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n+2 => fib (n+1) + fib n

theorem fib_step (n : Nat) : fib (n+2) = fib (n+1) + fib n := rfl

theorem fib_mono (n : Nat) : fib n ≤ fib (n+1) := by
  cases n with
  | zero => decide
  | succ n => rw [fib_step]; omega

theorem fib_positive (n : Nat) : 1 ≤ fib (n+1) := by
  induction n with
  | zero => decide
  | succ n ih => rw [fib_step]; omega

theorem fib_double (n : Nat) : fib (n+2) ≤ 2*fib (n+1) := by
  have mono := fib_mono n
  rw [fib_step]
  omega

theorem fib_four (n : Nat) : fib (n+6) ≤ 8*fib (n+2) := by
  have bound : fib (n+3) ≤ 2*fib (n+2) := fib_double (n+1)
  have r4 : fib (n+4)=fib (n+3)+fib (n+2) := rfl
  have r5 : fib (n+5)=fib (n+4)+fib (n+3) := rfl
  have r6 : fib (n+6)=fib (n+5)+fib (n+4) := rfl
  rw [r6,r5,r4]
  omega

theorem fib_power_bound (b : Nat) : fib (b+2) ≤ 2^(b-b/4) := by
  induction b using Nat.strongInductionOn with
  | ind b ih =>
    by_cases small : b < 4
    · cases b with
      | zero => decide
      | succ b => cases b with
        | zero => decide
        | succ b => cases b with
          | zero => decide
          | succ b =>
            have last : b=0 := by omega
            subst b
            decide
    · have previous := ih (b-4) (by omega)
      have jump := fib_four (b-4)
      have position : b-4+6=b+2 := by omega
      rw [position] at jump
      have scaled := Nat.mul_le_mul_left 8 previous
      have exponent : 3+((b-4)-(b-4)/4)=b-b/4 := by omega
      calc
        fib (b+2) ≤ 8*2^((b-4)-(b-4)/4) := Nat.le_trans jump scaled
        _ = 2^(3+((b-4)-(b-4)/4)) := (Nat.pow_add 2 3 _).symm
        _ = 2^(b-b/4) := by rw [exponent]

theorem first_two {r : Nat} (c : Chain r) (bound : 1 ≤ r) : c.value 1 = 2 := by
  obtain ⟨hl,hr,recipe⟩ := c.valid 1 (by decide) bound
  have left : c.left 1=0 := by omega
  have right : c.right 1=0 := by omega
  rw [left,right,c.initial] at recipe
  have large := at_least_two c (by decide : 0<1) bound
  cases flag : c.isMul 1 <;> simp only [flag, Bool.false_eq_true, if_false, if_true] at recipe <;> omega

-- Count only instructions after the mandatory first write 1+1=2.
inductive Counted {r : Nat} (c : Chain r) : Nat → Nat → Nat → Prop
  | first (bound : 1 ≤ r) : Counted c 1 0 0
  | square {i b d : Nat} (previous : Counted c i b d)
      (bound : i+1 ≤ r) (sq : Square c (i+1)) : Counted c (i+1) b (d+1)
  | other {i b d : Nat} (previous : Counted c i b d)
      (bound : i+1 ≤ r) (non : ¬ Square c (i+1)) : Counted c (i+1) (b+1) d

theorem counted_length {r i b d : Nat} {c : Chain r} (h : Counted c i b d) :
    i = 1+b+d := by
  induction h <;> omega

theorem counts_exist {r : Nat} (c : Chain r) (i : Nat) (positive : 1 ≤ i) (bound : i ≤ r) :
    ∃ b d, Counted c i b d := by
  induction i with
  | zero => omega
  | succ i ih =>
    cases i with
    | zero => exact ⟨0,0,Counted.first bound⟩
    | succ i =>
      obtain ⟨b,d,previous⟩ := ih (by omega) (by omega)
      by_cases sq : Square c (i+2)
      · exact ⟨b,d+1,Counted.square previous bound sq⟩
      · exact ⟨b+1,d,Counted.other previous bound sq⟩

theorem nonsquare_product_bound {r i X Y : Nat} (c : Chain r)
    (positive : 1 ≤ i) (bound : i+1 ≤ r)
    (head : c.value i ≤ X) (second : c.value (i-1) ≤ Y) (large : 2 ≤ Y)
    (non : ¬ Square c (i+1)) : c.value (i+1) ≤ X*Y := by
  obtain ⟨hl,hr,recipe⟩ := c.valid (i+1) (by omega) bound
  have left := Nat.le_trans (monotone c (by omega : c.left (i+1) ≤ i) (by omega)) head
  have right := Nat.le_trans (monotone c (by omega : c.right (i+1) ≤ i) (by omega)) head
  cases flag : c.isMul (i+1)
  · simp only [flag,Bool.false_eq_true,if_false] at recipe
    have addition := Nat.add_le_add left right
    have multiplier := Nat.mul_le_mul_left X large
    rw [Nat.mul_two] at multiplier
    omega
  · simp only [flag,if_true] at recipe
    by_cases oldLeft : c.left (i+1) ≤ i-1
    · have earlier := Nat.le_trans (monotone c oldLeft (by omega)) second
      have product := Nat.mul_le_mul earlier right
      rw [Nat.mul_comm Y X] at product
      omega
    · have latest : c.left (i+1) = i := by omega
      have oldRight : c.right (i+1) ≤ i-1 := by
        apply Classical.byContradiction
        intro notOld
        have latestRight : c.right (i+1)=i := by omega
        apply non
        simp only [Square, Nat.add_sub_cancel]
        simpa only [latest,latestRight] using recipe
      have earlier := Nat.le_trans (monotone c oldRight (by omega)) second
      have product := Nat.mul_le_mul left earlier
      omega

theorem doubled_power (d t : Nat) :
    2^(2^(d+1)*t) = 2^(2^d*t)*2^(2^d*t) := by
  rw [Nat.pow_succ, Nat.mul_two, Nat.add_mul, Nat.pow_add]

theorem envelope {r i b d : Nat} {c : Chain r} (h : Counted c i b d) :
    c.value i ≤ 2^(2^d*fib (b+2)) ∧
    c.value (i-1) ≤ 2^(2^d*fib (b+1)) := by
  induction h with
  | first bound =>
    rw [first_two c bound, c.initial]
    decide
  | @square i b d _previous _bound sq ih =>
    have next : c.value (i+1)=c.value i*c.value i := by
      simpa only [Square,Nat.add_sub_cancel] using sq
    constructor
    · rw [next,doubled_power]
      exact Nat.mul_le_mul ih.1 ih.1
    · simp only [Nat.add_sub_cancel]
      have exponents := Nat.mul_le_mul_left (2^d) (fib_double b)
      have powers := Nat.pow_le_pow_of_le (by decide : 1<2) exponents
      have target : 2^d*(2*fib (b+1))=2^(d+1)*fib (b+1) := by
        rw [Nat.pow_succ,Nat.mul_assoc]
      rw [target] at powers
      exact Nat.le_trans ih.1 powers
  | @other i b d previous bound non ih =>
    have len := counted_length previous
    have exponentPositive : 1 ≤ 2^d*fib (b+1) :=
      Nat.mul_le_mul (Nat.one_le_two_pow) (fib_positive b)
    have two : 2 ≤ 2^(2^d*fib (b+1)) := by
      simpa only [Nat.pow_one] using
        Nat.pow_le_pow_of_le (by decide : 1<2) exponentPositive
    have product := nonsquare_product_bound c (by omega) bound ih.1 ih.2 two non
    constructor
    · have sum : fib (b+1+2)=fib (b+2)+fib (b+1) := fib_step (b+1)
      rw [sum,Nat.mul_add,Nat.pow_add]
      exact product
    · simpa only [Nat.add_sub_cancel] using ih.1

theorem bounded_nonsquares {r i b d L s : Nat} {c : Chain r}
    (counts : Counted c i b d) (positiveLevel : 1 ≤ L)
    (reachesLevel : 2^(2^(L-1)) ≤ c.value i) (budget : i ≤ L+s) :
    b+1 ≤ 4*s+4 := by
  have head := (envelope counts).1
  have fibBound := Nat.mul_le_mul_left (2^d) (fib_power_bound b)
  rw [← Nat.pow_add] at fibBound
  have upper := Nat.pow_le_pow_of_le (by decide : 1<2) fibBound
  have compare := Nat.le_trans reachesLevel (Nat.le_trans head upper)
  have first := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp compare
  have second := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp first
  have len := counted_length counts
  omega



def nonsquares {r : Nat} (c : Chain r) : Nat → Nat
  | 0 => 0
  | i+1 => nonsquares c i +
      if c.value (i+1) = c.value i*c.value i then 0 else 1

theorem counted_canonical {r i b d : Nat} {c : Chain r} (h : Counted c i b d) :
    nonsquares c i = b+1 := by
  induction h with
  | first bound =>
    simp only [nonsquares,first_two c bound,c.initial]
    decide
  | @square i b _d _ _ sq ih =>
    have eq : c.value (i+1)=c.value i*c.value i := by
      simpa only [Square,Nat.add_sub_cancel] using sq
    simp only [nonsquares,eq,if_true,ih,Nat.add_zero]
  | @other i b _d _ _ non ih =>
    have ne : ¬ c.value (i+1)=c.value i*c.value i := by
      simpa only [Square,Nat.add_sub_cancel] using non
    simp only [nonsquares,ne,if_false,ih]

theorem tower_large (n : Nat) : 2 ≤ 2^(2^n) := by
  simpa only [Nat.pow_one] using
    Nat.pow_le_pow_of_le (by decide : 1<2) (Nat.one_le_two_pow (n := n))

theorem chain_nonsquare_bound {r L s : Nat} (c : Chain r)
    (positiveLevel : 1 ≤ L) (reachesLevel : 2^(2^(L-1)) ≤ c.value r)
    (budget : r ≤ L+s) : nonsquares c r ≤ 4*s+4 := by
  have positive : 1 ≤ r := by
    by_cases zero : r=0
    · subst r
      rw [c.initial] at reachesLevel
      have large := tower_large (L-1)
      omega
    · omega
  obtain ⟨b,d,counts⟩ := counts_exist c r positive (Nat.le_refl _)
  rw [counted_canonical counts]
  exact bounded_nonsquares counts positiveLevel reachesLevel budget

theorem tower_step (n : Nat) : 2^(2^(n+1)) = 2^(2^n)*2^(2^n) := by
  simpa only [Nat.mul_one] using doubled_power n 1

theorem mersenne_reaches_level {n : Nat} (positive : 1 ≤ n) :
    2^(2^(n-1)) ≤ 2^(2^n)-1 := by
  cases n with
  | zero => omega
  | succ k =>
    have large := tower_large k
    have mul := Nat.mul_le_mul_left (2^(2^k)) large
    rw [Nat.mul_two] at mul
    simp only [Nat.add_sub_cancel, tower_step]
    omega

theorem mersenne_nonsquare_bound {r n excess : Nat} (c : Chain r)
    (positive : 1 ≤ n) (endpoint : c.value r = 2^(2^n)-1)
    (budget : r ≤ n+excess) : nonsquares c r ≤ 4*excess+4 := by
  apply chain_nonsquare_bound c positive
  · rw [endpoint]
    exact mersenne_reaches_level positive
  · exact budget



theorem tower_as_squares (n : Nat) : 2^(2^n) = SolvedCompression.iterSq n 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tower_step,ih]
    rfl

end SolvedGrowth
