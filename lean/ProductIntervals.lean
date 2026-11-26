import Lean

namespace SolvedProducts

-- The strict interval width forces a unique integral neighbor.
theorem transport {a b lower upper : Nat}
    (lo : lower ≤ a*b) (hi : a*b ≤ upper) (width : upper-lower < a) :
    upper / a = b := by
  apply Nat.div_eq_of_lt_le
  · simpa only [Nat.mul_comm] using hi
  · rw [Nat.succ_mul]
    have base : lower ≤ b*a := by simpa only [Nat.mul_comm] using lo
    omega

theorem unique_neighbor {a b c lower upper : Nat}
    (bl : lower ≤ a*b) (bh : a*b ≤ upper)
    (cl : lower ≤ a*c) (ch : a*c ≤ upper) (width : upper-lower < a) : b=c := by
  exact (transport bl bh width).symm.trans (transport cl ch width)

-- The hypothesis is confined to the finite search interval. The arithmetic
-- composition and its non-increasing property remain part of the manuscript.
theorem fixed_point_unique (f : Nat → Nat) {lo hi a b : Nat}
    (anti : ∀ x y, lo ≤ x → y ≤ hi → x ≤ y → f y ≤ f x)
    (al : lo ≤ a) (ah : a ≤ hi) (bl : lo ≤ b) (bh : b ≤ hi)
    (fa : f a = a) (fb : f b = b) : a=b := by
  by_cases h : a ≤ b
  · have rev := anti a b al bh h
    rw [fa,fb] at rev
    omega
  · have rev := anti b a bl ah (by omega)
    rw [fa,fb] at rev
    omega

#print axioms transport
#print axioms unique_neighbor
#print axioms fixed_point_unique
end SolvedProducts
