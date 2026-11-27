import Formal.ICG.EvenPacked
import Research.ICGGeneralBridge

/-!
# Maximal energy of integral circulant graphs `ICG(2^a p^b, S)` from a certificate

H. Dong's bridge `ICGGeneral.energy_icgAdj_pq` (ai4math-results, Apache-2.0) identifies the
energy of `ICG(2^a p^b, S)` with `L1mat 2 p a b` of the indicator of `S` on the exponent box.
For a set `S` of proper divisors the indicator is `ind b (maskOfDivs a b p S)`, and masks of
length `(a+1)(b+1) - 1` correspond exactly to sets of proper divisors (`divsOfMask`). So a
successful `certifyP` bounds the energy of every `ICG(2^a p^b, S)` by `E(p)` and names the sets
attaining it (`energy_le_of_certifyP`).
-/

namespace Solved.ICG

open Solved.Cert Finset

/-- The mask of a set of divisors of `2^a p^b`: cell `k = c(b+1)+e` is set iff `2^c p^e ∈ S`. -/
def maskOfDivs (a b p : ℕ) (S : Finset ℕ) : List Bool :=
  (List.range ((a + 1) * (b + 1) - 1)).map fun k =>
    decide (2 ^ (k / (b + 1)) * p ^ (k % (b + 1)) ∈ S)

/-- The set of divisors `2^c p^e` whose cells a mask selects. -/
def divsOfMask (a b p : ℕ) (L : List Bool) : Finset ℕ :=
  (((List.range ((a + 1) * (b + 1) - 1)).filter (bit L)).map fun k =>
    2 ^ (k / (b + 1)) * p ^ (k % (b + 1))).toFinset

theorem bit_eq_getD (L : List Bool) (k : ℕ) : bit L k = L.getD k false := by
  induction L generalizing k with
  | nil => simp
  | cons c L ih => cases k <;> simp [ih]

theorem bit_map_range (n : ℕ) (f : ℕ → Bool) (k : ℕ) :
    bit ((List.range n).map f) k = (decide (k < n) && f k) := by
  by_cases hk : k < n
  · rw [bit_eq_getD, List.getD_eq_getElem?_getD]
    simp [hk]
  · rw [bit_of_length_le (by simpa using hk)]
    simp [hk]

theorem length_maskOfDivs (a b p : ℕ) (S : Finset ℕ) :
    (maskOfDivs a b p S).length = (a + 1) * (b + 1) - 1 := by
  simp [maskOfDivs]

theorem top_cell {a b c e : ℕ} (hc : c ≤ a) (he : e ≤ b) :
    c * (b + 1) + e < (a + 1) * (b + 1) - 1 ∨ (c = a ∧ e = b) := by
  by_cases h : c = a ∧ e = b
  · exact Or.inr h
  · left
    have h1 : c * (b + 1) ≤ a * (b + 1) := Nat.mul_le_mul_right _ hc
    have h2 : (a + 1) * (b + 1) = a * (b + 1) + b + 1 := by ring
    rcases Nat.lt_or_ge c a with hca | hca
    · have : (c + 1) * (b + 1) ≤ a * (b + 1) := Nat.mul_le_mul_right _ hca
      have : (c + 1) * (b + 1) = c * (b + 1) + b + 1 := by ring
      omega
    · have hce : c = a := le_antisymm hc hca
      subst hce
      have : e < b := lt_of_le_of_ne he fun h' => h ⟨rfl, h'⟩
      omega

/-- On the exponent box the mask's indicator is the indicator of `S`, if `S` omits the order. -/
theorem ind_maskOfDivs {a b p : ℕ} {S : Finset ℕ} (hS : 2 ^ a * p ^ b ∉ S) {c e : ℕ}
    (hc : c ≤ a) (he : e ≤ b) :
    ind b (maskOfDivs a b p S) c e = if 2 ^ c * p ^ e ∈ S then 1 else 0 := by
  unfold ind maskOfDivs
  rw [bit_map_range, flat_div c (Nat.lt_succ_of_le he), flat_mod c (Nat.lt_succ_of_le he)]
  rcases top_cell hc he with h | ⟨hca, heb⟩
  · simp [h]
  · have hk : ¬ (c * (b + 1) + e < (a + 1) * (b + 1) - 1) := by
      rw [hca, heb]
      have : (a + 1) * (b + 1) = a * (b + 1) + b + 1 := by ring
      omega
    have hS' : 2 ^ c * p ^ e ∉ S := by rw [hca, heb]; exact hS
    simp [hk, hS']

/-- `L1mat` only reads the indicator on the exponent box. -/
theorem L1mat_congr {p q : ℝ} {a b : ℕ} {Y Y' : ℕ → ℕ → ℝ}
    (h : ∀ c ≤ a, ∀ e ≤ b, Y c e = Y' c e) : ICGGeneral.L1mat p q a b Y = ICGGeneral.L1mat p q a b Y' := by
  unfold ICGGeneral.L1mat ICGGeneral.Mentry
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  congr 1
  refine sum_congr rfl fun i hi => sum_congr rfl fun l hl => ?_
  rw [h i (Nat.lt_succ_iff.1 (mem_range.1 hi)) l (Nat.lt_succ_iff.1 (mem_range.1 hl))]

/-- The energy of `ICG(2^a p^b, S)` for a set `S` of proper divisors, through Dong's bridge. -/
theorem energy_eq_L1mat {a b p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S : Finset ℕ}
    (hS : S ⊆ (2 ^ a * p ^ b).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) =
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b (maskOfDivs a b p S)) := by
  have hn : 2 ^ a * p ^ b ∉ S := fun h => lt_irrefl _ (Nat.mem_properDivisors.1 (hS h)).2
  rw [ICGGeneral.energy_icgAdj_pq 2 p a b Nat.prime_two hp (Ne.symm hp2) S]
  push_cast
  exact L1mat_congr fun c hc e he => (ind_maskOfDivs hn hc he).symm

/-! ## Masks and sets of proper divisors -/

theorem mem_divsOfMask {a b p : ℕ} {L : List Bool} {x : ℕ} :
    x ∈ divsOfMask a b p L ↔
      ∃ k < (a + 1) * (b + 1) - 1, bit L k = true ∧ 2 ^ (k / (b + 1)) * p ^ (k % (b + 1)) = x := by
  simp [divsOfMask, List.mem_filter, and_assoc]

theorem divsOfMask_maskOfDivs {a b p : ℕ} (hp : p.Prime) {S : Finset ℕ}
    (hS : S ⊆ (2 ^ a * p ^ b).properDivisors) : divsOfMask a b p (maskOfDivs a b p S) = S := by
  ext x
  rw [mem_divsOfMask]
  constructor
  · rintro ⟨k, hk, hb, rfl⟩
    rw [maskOfDivs, bit_map_range] at hb
    simpa [hk] using hb
  · intro hx
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.1 (hS hx)
    obtain ⟨c, hc, e, he, rfl⟩ := ICGGeneral.pq_dvd_rep Nat.prime_two hp hdvd
    rcases top_cell hc he with h | ⟨rfl, rfl⟩
    · refine ⟨c * (b + 1) + e, h, ?_, ?_⟩
      · rw [maskOfDivs, bit_map_range, flat_div c (Nat.lt_succ_of_le he),
          flat_mod c (Nat.lt_succ_of_le he)]
        simp [h, hx]
      · rw [flat_div c (Nat.lt_succ_of_le he), flat_mod c (Nat.lt_succ_of_le he)]
    · exact absurd hlt (lt_irrefl _)

theorem maskOfDivs_divsOfMask {a b p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : List Bool}
    (hL : L.length = (a + 1) * (b + 1) - 1) : maskOfDivs a b p (divsOfMask a b p L) = L := by
  refine bit_ext (by rw [length_maskOfDivs, hL]) fun k hk => ?_
  rw [length_maskOfDivs] at hk
  rw [maskOfDivs, bit_map_range]
  simp only [hk, decide_true, Bool.true_and]
  rw [Bool.eq_iff_iff, decide_eq_true_iff, mem_divsOfMask]
  constructor
  · rintro ⟨k', hk', hb, hEq⟩
    obtain ⟨h1, h2⟩ := (ICGGeneral.pq_inj Nat.prime_two hp (Ne.symm hp2)).1 hEq
    have : k' = k := by
      rw [← Nat.div_add_mod k' (b + 1), ← Nat.div_add_mod k (b + 1), h1, h2]
    exact this ▸ hb
  · intro hb
    exact ⟨k, hk, hb, rfl⟩

/-! ## The graph-energy theorem -/

/-- What a successful packed certificate proves about integral circulant graphs: for every odd
prime `p ≥ p₀` and every set `S` of proper divisors of `n = 2^a p^b`, the energy of
`ICG(n, S)` is at most `E(p)`, with equality exactly for the divisor sets of the certified
maximisers. -/
theorem energy_le_of_certifyP {a b p0 w D : ℕ} {E : UPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certifyP a b p0 w D E ks star others = true) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hp0 : p0 ≤ p) {S : Finset ℕ}
    (hS : S ⊆ (2 ^ a * p ^ b).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((UPoly.eval E p : ℤ) : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) =
          ((UPoly.eval E p : ℤ) : ℝ) ↔ S ∈ (star :: others).map (divsOfMask a b p)) := by
  obtain ⟨hmax, hlt⟩ := certifyP_sound h (p := p) (by exact_mod_cast hp0)
  rw [energy_eq_L1mat hp hp2 hS]
  have hlen := length_maskOfDivs a b p S
  by_cases hmem : maskOfDivs a b p S ∈ star :: others
  · have heq := (hmax _ hmem).2
    push_cast at heq
    refine ⟨heq.le, ⟨fun _ => ?_, fun _ => heq⟩⟩
    exact List.mem_map.2 ⟨_, hmem, divsOfMask_maskOfDivs hp hS⟩
  · have hl := hlt _ hlen hmem
    push_cast at hl
    refine ⟨hl.le, ⟨fun he => absurd he hl.ne, fun hS' => ?_⟩⟩
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hS'
    exact absurd (by rw [maskOfDivs_divsOfMask hp hp2 (hmax L hL).1]; exact hL) hmem

end Solved.ICG
