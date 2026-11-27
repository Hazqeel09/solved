import Mathlib.Tactic

/-!
# Fields packed into one natural number

`pack w n f = ∑_{i<n} f i · 2^{w i}` holds `n` fields of `w` bits. While every field is below
`2^w` the fields can be read back with division and remainder by powers of two, and bitwise
`and` acts fieldwise. The kernel evaluates `+ - * / % &&& >>>` on natural-number literals with
GMP, so a check phrased on whole packed numbers costs a handful of kernel steps per operation
instead of a list traversal per field.

Signed fields use the offset `2^{w-1}`: `enc w n f` stores `f i + 2^{w-1}`, and `posPack`
extracts the fieldwise positive part with two `and`s, a shift and a multiplication.
-/

namespace Solved.Cert.Pack

open Finset

/-- `∑_{i<n} f i · 2^{w i}`. -/
def pack (w n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ i ∈ range n, f i * 2 ^ (w * i)

@[simp] theorem pack_zero (w : ℕ) (f : ℕ → ℕ) : pack w 0 f = 0 := by simp [pack]

theorem pack_succ (w n : ℕ) (f : ℕ → ℕ) :
    pack w (n + 1) f = f 0 + 2 ^ w * pack w n (fun i => f (i + 1)) := by
  unfold pack
  rw [sum_range_succ', mul_sum, add_comm]
  simp only [Nat.mul_zero, pow_zero, Nat.mul_one]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.mul_succ, pow_add]; ring

theorem pack_congr {w n : ℕ} {f g : ℕ → ℕ} (h : ∀ i < n, f i = g i) :
    pack w n f = pack w n g :=
  sum_congr rfl fun i hi => by rw [h i (mem_range.1 hi)]

theorem pack_add (w n : ℕ) (f g : ℕ → ℕ) :
    pack w n (fun i => f i + g i) = pack w n f + pack w n g := by
  simp [pack, add_mul, sum_add_distrib]

theorem pack_mul_left (w n c : ℕ) (f : ℕ → ℕ) :
    pack w n (fun i => c * f i) = c * pack w n f := by
  simp [pack, mul_sum, mul_assoc]

theorem pack_sum {ι : Type*} (s : Finset ι) (w n : ℕ) (F : ι → ℕ → ℕ) :
    pack w n (fun i => ∑ j ∈ s, F j i) = ∑ j ∈ s, pack w n (F j) := by
  simp only [pack, sum_mul]; exact sum_comm

theorem pack_lt {w n : ℕ} {f : ℕ → ℕ} (h : ∀ i < n, f i < 2 ^ w) : pack w n f < 2 ^ (w * n) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pack_succ]
    have h0 := h 0 (Nat.succ_pos n)
    have h1 := ih (f := fun i => f (i + 1)) fun i hi => h (i + 1) (by omega)
    calc f 0 + 2 ^ w * pack w n (fun i => f (i + 1))
        < 2 ^ w + 2 ^ w * pack w n (fun i => f (i + 1)) := by omega
      _ = 2 ^ w * (pack w n (fun i => f (i + 1)) + 1) := by ring
      _ ≤ 2 ^ w * 2 ^ (w * n) := Nat.mul_le_mul_left _ h1
      _ = 2 ^ (w * (n + 1)) := by rw [← pow_add]; congr 1; ring

theorem pack_split (w k n : ℕ) (f : ℕ → ℕ) :
    pack w (k + n) f = pack w k f + 2 ^ (w * k) * pack w n (fun i => f (k + i)) := by
  unfold pack
  rw [sum_range_add, mul_sum]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Nat.mul_add, pow_add]; ring

/-- Fields `k, …, k+n-1` of a packed number with valid fields. -/
theorem pack_block {w k n N : ℕ} {f : ℕ → ℕ} (hN : k + n ≤ N) (h : ∀ i < N, f i < 2 ^ w) :
    pack w N f / 2 ^ (w * k) % 2 ^ (w * n) = pack w n (fun i => f (k + i)) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [Nat.add_assoc, pack_split w k (n + r), pack_split w n r]
  have hA : pack w k f < 2 ^ (w * k) := pack_lt fun i hi => h i (by omega)
  have hB : pack w n (fun i => f (k + i)) < 2 ^ (w * n) :=
    pack_lt fun i hi => h (k + i) (by omega)
  rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hA, Nat.zero_add,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hB]

theorem pack_mod {w n : ℕ} {f : ℕ → ℕ} (h0 : f 0 < 2 ^ w) :
    pack w (n + 1) f % 2 ^ w = f 0 := by
  rw [pack_succ, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]

theorem pack_div {w n : ℕ} {f : ℕ → ℕ} (h0 : f 0 < 2 ^ w) :
    pack w (n + 1) f / 2 ^ w = pack w n (fun i => f (i + 1)) := by
  rw [pack_succ, Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add]

theorem pack_inj {w n : ℕ} {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w) (hg : ∀ i < n, g i < 2 ^ w)
    (h : pack w n f = pack w n g) : ∀ i < n, f i = g i := by
  induction n generalizing f g with
  | zero => intro i hi; omega
  | succ n ih =>
    have hf0 := hf 0 (by omega)
    have hg0 := hg 0 (by omega)
    have h0 : f 0 = g 0 := by rw [← pack_mod (n := n) hf0, ← pack_mod (n := n) hg0, h]
    have ht : pack w n (fun i => f (i + 1)) = pack w n (fun i => g (i + 1)) := by
      rw [← pack_div hf0, ← pack_div hg0, h]
    intro i hi
    cases i with
    | zero => exact h0
    | succ i =>
      exact ih (fun j hj => hf (j + 1) (by omega)) (fun j hj => hg (j + 1) (by omega)) ht i
        (by omega)

/-- Bitwise `and` acts fieldwise on valid fields. -/
theorem pack_land {w n : ℕ} {f g : ℕ → ℕ} (hf : ∀ i < n, f i < 2 ^ w)
    (hg : ∀ i < n, g i < 2 ^ w) :
    pack w n f &&& pack w n g = pack w n (fun i => f i &&& g i) := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih =>
    have hf0 := hf 0 (by omega)
    have hg0 := hg 0 (by omega)
    rw [pack_succ, pack_succ, pack_succ,
      ← ih (fun i hi => hf (i + 1) (by omega)) (fun i hi => hg (i + 1) (by omega))]
    apply Nat.eq_of_testBit_eq
    intro j
    rw [add_comm (f 0), add_comm (g 0), add_comm (f 0 &&& g 0), Nat.testBit_and,
      Nat.testBit_two_pow_mul_add _ hf0, Nat.testBit_two_pow_mul_add _ hg0,
      Nat.testBit_two_pow_mul_add _ (Nat.and_lt_two_pow _ hg0)]
    split_ifs <;> simp [Nat.testBit_and]

/-! ## Single fields -/

theorem testBit_top {f k : ℕ} (hf : f < 2 ^ (k + 1)) : f.testBit k = decide (2 ^ k ≤ f) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.lt_or_ge f (2 ^ k) with h | h
  · rw [Nat.div_eq_of_lt h]; simp [Nat.not_le.2 h]
  · have h1 : 1 ≤ f / 2 ^ k := (Nat.le_div_iff_mul_le (by positivity)).2 (by simpa using h)
    have h2 : f / 2 ^ k < 2 := by
      rw [Nat.div_lt_iff_lt_mul (by positivity)]; rw [pow_succ] at hf; omega
    have : f / 2 ^ k = 1 := by omega
    rw [this]; simp [h]

theorem land_two_pow {f k : ℕ} (hf : f < 2 ^ (k + 1)) :
    f &&& 2 ^ k = if 2 ^ k ≤ f then 2 ^ k else 0 := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  by_cases hj : k = j
  · subst hj
    rw [testBit_top hf]
    split_ifs with h <;> simp [h]
  · split_ifs <;> simp [hj]

/-! ## The fieldwise positive part of offset-encoded fields -/

/-- `pack` of the constant field `c`. -/
def rep (w n c : ℕ) : ℕ := pack w n fun _ => c

/-- Fieldwise `F i - 2^{w-1}` where `F i ≥ 2^{w-1}`, else `0`, for `w`-bit fields. -/
def posPack (w OO X : ℕ) : ℕ := X &&& ((X &&& OO) >>> (w - 1)) * (2 ^ (w - 1) - 1)

theorem posPack_spec {w n : ℕ} (hw : 0 < w) {F : ℕ → ℕ} (hF : ∀ i < n, F i < 2 ^ w) :
    posPack w (rep w n (2 ^ (w - 1))) (pack w n F) =
      pack w n (fun i => if 2 ^ (w - 1) ≤ F i then F i - 2 ^ (w - 1) else 0) := by
  obtain ⟨v, rfl⟩ : ∃ v, w = v + 1 := ⟨w - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hO : 2 ^ v < 2 ^ (v + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- guards `2^v · [2^v ≤ F i]`
  have hG : pack (v + 1) n F &&& rep (v + 1) n (2 ^ v) =
      2 ^ v * pack (v + 1) n (fun i => if 2 ^ v ≤ F i then 1 else 0) := by
    rw [rep, pack_land hF (fun _ _ => hO), ← pack_mul_left]
    refine pack_congr fun i hi => ?_
    rw [land_two_pow (hF i hi)]
    split_ifs <;> simp
  -- spread masks `(2^v - 1) · [2^v ≤ F i]`
  have hM : (pack (v + 1) n F &&& rep (v + 1) n (2 ^ v)) >>> v * (2 ^ v - 1) =
      pack (v + 1) n (fun i => (2 ^ v - 1) * if 2 ^ v ≤ F i then 1 else 0) := by
    rw [hG, Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel_left _ (by positivity),
      pack_mul_left, Nat.mul_comm]
  unfold posPack
  simp only [Nat.add_sub_cancel]
  rw [hM, pack_land hF fun i _ => by split_ifs <;> omega]
  refine pack_congr fun i hi => ?_
  split_ifs with h
  · have := hF i hi
    rw [pow_succ] at this
    rw [Nat.mul_one, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_sub_mod h,
      Nat.mod_eq_of_lt (by omega)]
  · simp

/-! ## Horizontal sums of blocks -/

/-- `∑_{e<m}` of the blocks of `D` fields of `P`. -/
def hsum (w D P : ℕ) : ℕ → ℕ
  | 0 => 0
  | e + 1 => hsum w D P e + (P >>> (w * D * e)) % 2 ^ (w * D)

theorem hsum_spec {w D m : ℕ} {f : ℕ → ℕ} (hf : ∀ i < m * D, f i < 2 ^ w) :
    hsum w D (pack w (m * D) f) m = pack w D (fun d => ∑ e ∈ range m, f (e * D + d)) := by
  rw [pack_sum]
  suffices ∀ e ≤ m, hsum w D (pack w (m * D) f) e =
      ∑ j ∈ range e, pack w D (fun d => f (j * D + d)) from this m le_rfl
  intro e he
  induction e with
  | zero => rfl
  | succ e ih =>
    rw [hsum, ih (by omega), sum_range_succ, Nat.shiftRight_eq_div_pow, Nat.mul_assoc,
      pack_block (k := D * e) (n := D) (N := m * D) (by nlinarith) hf]
    congr 1
    refine pack_congr fun d _ => ?_
    rw [Nat.mul_comm D e]

end Solved.Cert.Pack
