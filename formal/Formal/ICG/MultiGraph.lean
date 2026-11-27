import Formal.ICG.MultiPacked
import Formal.ICG.EvenGraph

/-!
# Maximal energy of multi-prime integral circulant graphs from a certificate

The primes of a `Shape` at `(p, q)` are `rOf s p q`. If they are distinct primes and the region
coordinates `x, y ≥ 0` give `σ₁ = p`, `σ₂ = q`, then the spectral bridge `energy_icgAdj_multi`
turns `certifyM_sound` into a bound on the energy of every `ICG(n, S)`, with `n = ∏ rᵢ^{aᵢ}` and
`S` a set of proper divisors, with equality exactly for the certified divisor sets
(`energy_le_of_certifyM`).
-/

namespace Solved.ICG.Multi

open Solved.Cert Finset

variable {k : ℕ}

/-- The primes of the order at `(p, q)`. -/
def rOf (s : Shape k) (p q : ℕ) (i : Fin k) : ℕ :=
  if s.slot i = 1 then p else if s.slot i = 2 then q else s.fixedP i

theorem prime_eq_rOf (s : Shape k) {p q : ℕ} {x y : ℤ} (h1 : s.σ1.val x y = p)
    (h2 : s.σ2.val x y = q) (i : Fin k) : s.prime x y i = (rOf s p q i : ℤ) := by
  unfold Shape.prime rOf
  split_ifs <;> simp [h1, h2]

/-! ## Divisor sets and masks -/

/-- The mask of a set of divisors: code `kc` is set iff `∏ rᵢ^{(dec kc)ᵢ} ∈ S`. -/
def maskOfDivs (r a : Fin k → ℕ) (S : Finset ℕ) : List Bool :=
  (List.range (size a - 1)).map fun kc => decide (pw r (dec a kc) ∈ S)

/-- The divisors whose codes a mask selects. -/
def divsOfMask (r a : Fin k → ℕ) (L : List Bool) : Finset ℕ :=
  (((List.range (size a - 1)).filter (bit L)).map fun kc => pw r (dec a kc)).toFinset

theorem length_maskOfDivs (r a : Fin k → ℕ) (S : Finset ℕ) :
    (maskOfDivs r a S).length = size a - 1 := by simp [maskOfDivs]

theorem bit_maskOfDivs (r a : Fin k → ℕ) (S : Finset ℕ) (kc : ℕ) :
    bit (maskOfDivs r a S) kc = (decide (kc < size a - 1) && decide (pw r (dec a kc) ∈ S)) := by
  rw [maskOfDivs, bit_map_range]

/-- Codes below `size a - 1` are the vectors other than the top. -/
theorem enc_lt_top {a x : Fin k → ℕ} (hx : x ∈ box a) (hne : x ≠ a) : enc a x < size a - 1 := by
  have h1 := enc_lt a hx
  have h2 : enc a x ≠ size a - 1 := fun h =>
    hne (enc_inj a hx (mem_box.2 fun i => le_rfl) (h.trans (enc_top a).symm))
  omega

theorem divsOfMask_maskOfDivs {r a : Fin k → ℕ} (hr : Primes r) {S : Finset ℕ}
    (hS : S ⊆ (pw r a).properDivisors) : divsOfMask r a (maskOfDivs r a S) = S := by
  ext d
  simp only [divsOfMask, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range,
    bit_maskOfDivs, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨kc, ⟨hkc, -, hmem⟩, rfl⟩
    exact hmem
  · intro hd
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.1 (hS hd)
    obtain ⟨x, hx, rfl⟩ := dvd_rep hr hdvd
    have hne : x ≠ a := by rintro rfl; exact lt_irrefl _ hlt
    refine ⟨enc a x, ⟨enc_lt_top hx hne, enc_lt_top hx hne, ?_⟩, ?_⟩ <;>
      rw [dec_enc a hx]
    exact hd

theorem maskOfDivs_divsOfMask {r a : Fin k → ℕ} (hr : Primes r) {L : List Bool}
    (hL : L.length = size a - 1) : maskOfDivs r a (divsOfMask r a L) = L := by
  refine bit_ext (by rw [length_maskOfDivs, hL]) fun kc hkc => ?_
  rw [length_maskOfDivs] at hkc
  rw [bit_maskOfDivs]
  simp only [hkc, decide_true, Bool.true_and]
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [divsOfMask, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨kc', ⟨hkc', hb⟩, hEq⟩
    have hv := (pw_inj hr).1 hEq
    have : kc' = kc := by
      rw [← enc_dec a (by omega : kc' < size a), hv, enc_dec a (by omega : kc < size a)]
    exact this ▸ hb
  · intro hb
    exact ⟨kc, ⟨hkc, hb⟩, rfl⟩

/-! ## From the bridge to the certificate's energy -/

theorem energy_eq_energyAt (s : Shape k) {p q : ℕ} {x y : ℤ} (h1 : s.σ1.val x y = p)
    (h2 : s.σ2.val x y = q) (hr : Primes (rOf s p q)) {S : Finset ℕ}
    (hS : S ⊆ (pw (rOf s p q) s.a).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S) (ICGBridge.icgAdj_isHermitian _ _) =
      ((energyAt s (maskOfDivs (rOf s p q) s.a S) x y : ℤ) : ℝ) := by
  have hn : pw (rOf s p q) s.a ∉ S := fun h =>
    lt_irrefl _ (Nat.mem_properDivisors.1 (hS h)).2
  rw [energy_icgAdj_multi hr, sum_box, energyAt]
  push_cast
  refine sum_congr rfl fun e he => ?_
  congr 1
  have hm : size s.a = (size s.a - 1) + 1 := (Nat.sub_add_cancel (size_pos s.a)).symm
  rw [sum_box, hm, sum_range_succ, ← hm, dec_top, ite_eq_right hn, add_zero]
  refine sum_congr rfl fun kc hkc => ?_
  rw [bit_maskOfDivs, decide_eq_true (mem_range.1 hkc), Bool.true_and]
  by_cases hmem : pw (rOf s p q) (dec s.a kc) ∈ S
  · simp only [hmem, decide_true, ite_true, s.cast_eval_cellB]
    exact prod_congr rfl fun i _ => by rw [prime_eq_rOf s h1 h2 i]; rfl
  · simp [hmem]

/-- What a successful multi-prime certificate proves about integral circulant graphs, at the
primes `p, q` of a point `(x, y)` of its region. -/
theorem energy_le_of_certifyM {s : Shape k} {w Dx Dy : ℕ} {E : BPoly} {ks : List ℕ}
    {star : List Bool} {others : List (List Bool)} (h : certifyM s w Dx Dy E ks star others = true)
    {p q : ℕ} {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) (h1 : s.σ1.val x y = p) (h2 : s.σ2.val x y = q)
    (hr : Primes (rOf s p q)) {S : Finset ℕ} (hS : S ⊆ (pw (rOf s p q) s.a).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((BPoly.eval E p q : ℤ) : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S)
          (ICGBridge.icgAdj_isHermitian _ _) = ((BPoly.eval E p q : ℤ) : ℝ) ↔
        S ∈ (star :: others).map (divsOfMask (rOf s p q) s.a)) := by
  obtain ⟨hmax, hlt⟩ := certifyM_sound h hx hy
  have htE : BPoly.eval (target s E) x y = BPoly.eval E p q := by
    rw [target, BPoly.eval_subst]
    have e1 : s.σ1.c0 + s.σ1.c1 * x + s.σ1.c2 * y = p := h1
    have e2 : s.σ2.c0 + s.σ2.c1 * x + s.σ2.c2 * y = q := h2
    rw [e1, e2]
  rw [energy_eq_energyAt s h1 h2 hr hS, ← htE]
  have hlen := length_maskOfDivs (rOf s p q) s.a S
  by_cases hmem : maskOfDivs (rOf s p q) s.a S ∈ star :: others
  · have heq := (hmax _ hmem).2
    refine ⟨by exact_mod_cast heq.le, ⟨fun _ => ?_, fun _ => by exact_mod_cast heq⟩⟩
    exact List.mem_map.2 ⟨_, hmem, divsOfMask_maskOfDivs hr hS⟩
  · have hl := hlt _ hlen hmem
    refine ⟨by exact_mod_cast hl.le, ⟨fun he => absurd (by exact_mod_cast he) hl.ne, fun hS' => ?_⟩⟩
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hS'
    exact absurd (by rw [maskOfDivs_divsOfMask hr (hmax L hL).1]; exact hL) hmem

/-! ## The two regions of the certificates -/

/-- Distinct odd primes differ by at least two. -/
theorem add_two_le_of_lt {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (h : p < q) : p + 2 ≤ q := by
  rcases hp.eq_two_or_odd with h1 | h1 <;> rcases hq.eq_two_or_odd with h2 | h2 <;> omega

/-- The region `p ≥ p₀, q ≥ p + 2`, with coordinates `p = p₀ + x`, `q = p₀ + 2 + x + y`. -/
theorem energy_le_lt {s : Shape k} {w Dx Dy : ℕ} {E : BPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certifyM s w Dx Dy E ks star others = true) {p0 : ℕ}
    (hσ1 : s.σ1 = ⟨(p0 : ℤ), 1, 0⟩) (hσ2 : s.σ2 = ⟨(p0 : ℤ) + 2, 1, 1⟩) {p q : ℕ} (hp0 : p0 ≤ p)
    (hpq : p + 2 ≤ q) (hr : Primes (rOf s p q)) {S : Finset ℕ}
    (hS : S ⊆ (pw (rOf s p q) s.a).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((BPoly.eval E p q : ℤ) : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S)
          (ICGBridge.icgAdj_isHermitian _ _) = ((BPoly.eval E p q : ℤ) : ℝ) ↔
        S ∈ (star :: others).map (divsOfMask (rOf s p q) s.a)) :=
  energy_le_of_certifyM h (x := (p : ℤ) - p0) (y := (q : ℤ) - p - 2) (by omega) (by omega)
    (by rw [hσ1, Affine.val]; ring) (by rw [hσ2, Affine.val]; ring) hr hS

/-- The region `q ≥ q₀, p ≥ q + 2`, with coordinates `q = q₀ + y`, `p = q₀ + 2 + x + y`. -/
theorem energy_le_gt {s : Shape k} {w Dx Dy : ℕ} {E : BPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certifyM s w Dx Dy E ks star others = true) {q0 : ℕ}
    (hσ1 : s.σ1 = ⟨(q0 : ℤ) + 2, 1, 1⟩) (hσ2 : s.σ2 = ⟨(q0 : ℤ), 0, 1⟩) {p q : ℕ} (hq0 : q0 ≤ q)
    (hqp : q + 2 ≤ p) (hr : Primes (rOf s p q)) {S : Finset ℕ}
    (hS : S ⊆ (pw (rOf s p q) s.a).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        ((BPoly.eval E p q : ℤ) : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (pw (rOf s p q) s.a) S)
          (ICGBridge.icgAdj_isHermitian _ _) = ((BPoly.eval E p q : ℤ) : ℝ) ↔
        S ∈ (star :: others).map (divsOfMask (rOf s p q) s.a)) :=
  energy_le_of_certifyM h (x := (p : ℤ) - q - 2) (y := (q : ℤ) - q0) (by omega) (by omega)
    (by rw [hσ1, Affine.val]; ring) (by rw [hσ2, Affine.val]; ring) hr hS

end Solved.ICG.Multi
