import Formal.Cert.BranchBound
import Formal.Cert.Sums
import Formal.ICG.LocalPoly
import Research.ICGGeneralThm5

/-!
# A reflective certificate for `ICGGeneral.L1mat 2 p a b`

For orders `2^a p^b` the reused bridge identifies the graph energy with `L1mat 2 p a b Y`,
where `Y` is the indicator of the divisor set on the exponent box `[0,a] × [0,b]`. Every entry
of `L1mat` is an integer polynomial in `p`, linear in the cells of the mask.

`certify` checks, by integer polynomial arithmetic that the kernel evaluates, that a claimed
list of maximising masks all have energy `E(p)` and that every other mask of the box without
its top cell (the order itself) has strictly smaller energy, for every integer `p ≥ p₀`. The
search over masks is `Solved.Cert.bnb`. `certify_sound` turns a successful check into that
statement about `L1mat`.
-/

namespace Solved.ICG

open Solved.Cert Finset

/-- `∑_{i < n} f i` as a polynomial. -/
def sumRange : ℕ → (ℕ → UPoly) → UPoly
  | 0, _ => []
  | n + 1, f => UPoly.add (sumRange n f) (f n)

@[simp] theorem eval_sumRange (n : ℕ) (f : ℕ → UPoly) (x : ℤ) :
    UPoly.eval (sumRange n f) x = ∑ i ∈ range n, UPoly.eval (f i) x := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, sum_range_succ]

/-- The indicator on the exponent box `[0,a] × [0,b]`, cell `(i,l)` at index `i(b+1)+l`. -/
def ind (b : ℕ) (L : List Bool) (i l : ℕ) : ℝ := if bit L (i * (b + 1) + l) then 1 else 0

/-- Entry `(u,v)` of `T_a(2) Y T_b(p)ᵀ` as a polynomial in `p`. -/
def entryP (a b : ℕ) (L : List Bool) (u v : ℕ) : UPoly :=
  sumRange (a + 1) fun i => sumRange (b + 1) fun l =>
    if bit L (i * (b + 1) + l) then UPoly.scale (UPoly.eval (tentP a u i) 2) (tentP b v l)
    else []

theorem eval_entryP (a b : ℕ) (L : List Bool) (u v : ℕ) (p : ℤ) :
    ((UPoly.eval (entryP a b L u v) p : ℤ) : ℝ) =
      ICGGeneral.Mentry 2 (p : ℝ) a b (ind b L) u v := by
  unfold entryP ICGGeneral.Mentry ind
  simp only [eval_sumRange, Int.cast_sum]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
  split_ifs with h
  · simp only [UPoly.eval_scale, Int.cast_mul, eval_tentP, Int.cast_ofNat]
    ring
  · simp

theorem L1mat_eq (a b : ℕ) (L : List Bool) (p : ℤ) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) =
      ∑ u ∈ range (a + 1), ∑ v ∈ range (b + 1),
        |((UPoly.eval (entryP a b L u v) p : ℤ) : ℝ)| := by
  unfold ICGGeneral.L1mat
  refine sum_congr rfl fun u _ => sum_congr rfl fun v _ => ?_
  rw [eval_entryP]

/-! ## Flat indices on the exponent box -/

/-- Contribution of cell `k = i(b+1)+l` to entry `e = u(b+1)+v`, a polynomial in `p`. -/
def cellP (a b k e : ℕ) : UPoly :=
  UPoly.scale (UPoly.eval (tentP a (e / (b + 1)) (k / (b + 1))) 2)
    (tentP b (e % (b + 1)) (k % (b + 1)))

/-- The contributions of cell `k` to every entry, as polynomials in `x = p - p₀`. -/
def cellTable (a b p0 k : ℕ) : Table :=
  (List.range ((a + 1) * (b + 1))).map fun e => UPoly.shift p0 (cellP a b k e)

theorem eval_entryP_flat (a b : ℕ) (L : List Bool) (e : ℕ) (p : ℤ) :
    UPoly.eval (entryP a b L (e / (b + 1)) (e % (b + 1))) p =
      ∑ k ∈ range ((a + 1) * (b + 1)), if bit L k then UPoly.eval (cellP a b k e) p else 0 := by
  rw [sum_range_mul_flat]
  unfold entryP
  simp only [eval_sumRange]
  refine sum_congr rfl fun i _ => sum_congr rfl fun l hl => ?_
  have hl' : l < b + 1 := mem_range.1 hl
  unfold cellP
  rw [flat_div i hl', flat_mod i hl']
  split_ifs <;> simp

theorem L1mat_flat (a b : ℕ) (L : List Bool) (p : ℤ) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) =
      ∑ e ∈ range ((a + 1) * (b + 1)),
        |((UPoly.eval (entryP a b L (e / (b + 1)) (e % (b + 1))) p : ℤ) : ℝ)| := by
  rw [L1mat_eq, sum_range_mul_flat]
  refine sum_congr rfl fun u _ => sum_congr rfl fun v hv => ?_
  rw [flat_div u (mem_range.1 hv), flat_mod u (mem_range.1 hv)]

/-! ## Exact energies of sign-certified masks -/

/-- Every entry below `m` has coefficients of one sign. -/
def signsOK (m : ℕ) (t : Table) : Bool :=
  (List.range m).all fun e => UPoly.allNonneg (t.get e) || UPoly.allNonpos (t.get e)

/-- A polynomial of certified constant sign, made nonnegative. -/
def signed (f : UPoly) : UPoly := if UPoly.allNonneg f then f else UPoly.neg f

theorem eval_signed {f : UPoly} (h : (UPoly.allNonneg f || UPoly.allNonpos f) = true) {x : ℤ}
    (hx : 0 ≤ x) : UPoly.eval (signed f) x = |UPoly.eval f x| := by
  unfold signed
  split_ifs with h₀
  · exact (abs_of_nonneg (UPoly.eval_nonneg_of_allNonneg h₀ hx)).symm
  · simp only [h₀, Bool.false_or] at h
    rw [UPoly.eval_neg, abs_of_nonpos (UPoly.eval_nonpos_of_allNonpos h hx)]

/-- `∑_{e < m} |tₑ|` for a sign-certified table. -/
def absSum (m : ℕ) (t : Table) : UPoly := sumRange m fun e => signed (t.get e)

theorem sum_abs_eq_absSum {m : ℕ} {t : Table} (h : signsOK m t = true) {x : ℤ} (hx : 0 ≤ x) :
    ∑ e ∈ range m, |UPoly.eval (t.get e) x| = UPoly.eval (absSum m t) x := by
  unfold absSum
  rw [eval_sumRange]
  refine sum_congr rfl fun e he => (eval_signed ?_ hx).symm
  exact List.all_eq_true.1 h e (by simpa using he)

/-! ## The certificate -/

/-- The decision steps for the cells `ks`, in that order. -/
def steps (a b p0 : ℕ) (ks : List ℕ) : List Step :=
  build (ks.map fun k => (k, cellTable a b p0 k))

/-- The certificate: `ks` orders the `(a+1)(b+1) - 1` cells below the top one; each mask in
`star :: others` (masks of that length) has energy `E(p)` exactly; every other mask has
energy below `E(p)`; all for `p ≥ p₀`. -/
def certify (a b p0 : ℕ) (E : UPoly) (ks : List ℕ) (star : List Bool)
    (others : List (List Bool)) : Bool :=
  let m := (a + 1) * (b + 1)
  let ss := steps a b p0 ks
  let target := UPoly.shift p0 E
  ks.isPerm (List.range (m - 1)) &&
    (star :: others).all (fun L => L.length == m - 1 && signsOK m (runAcc L ss []) &&
      UPoly.allZero (UPoly.add (absSum m (runAcc L ss [])) (UPoly.neg target))) &&
    bnb target (star :: others) ss (List.replicate (m - 1) false) []

theorem eval_runAcc_steps (a b p0 : ℕ) {ks : List ℕ}
    (hperm : ks.Perm (List.range ((a + 1) * (b + 1) - 1))) {L : List Bool}
    (hL : L.length = (a + 1) * (b + 1) - 1) {e : ℕ} (he : e < (a + 1) * (b + 1)) (p : ℤ) :
    UPoly.eval ((runAcc L (steps a b p0 ks) []).get e) (p - p0) =
      UPoly.eval (entryP a b L (e / (b + 1)) (e % (b + 1))) p := by
  have hm : (a + 1) * (b + 1) = ((a + 1) * (b + 1) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))).symm
  rw [steps, eval_runAcc_build L ks _ hperm, eval_entryP_flat, hm, sum_range_succ,
    bit_of_length_le hL.le, ← hm]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [cellTable, Table.get_map_range _ _ he, UPoly.eval_shift, sub_add_cancel]

theorem L1mat_eq_runAcc (a b p0 : ℕ) {ks : List ℕ}
    (hperm : ks.Perm (List.range ((a + 1) * (b + 1) - 1))) {L : List Bool}
    (hL : L.length = (a + 1) * (b + 1) - 1) (p : ℤ) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) =
      ((∑ e ∈ range ((a + 1) * (b + 1)),
        |UPoly.eval ((runAcc L (steps a b p0 ks) []).get e) (p - p0)| : ℤ) : ℝ) := by
  rw [L1mat_flat]
  push_cast
  refine sum_congr rfl fun e he => ?_
  rw [eval_runAcc_steps a b p0 hperm hL (mem_range.1 he)]

/-- A mask whose entries have certified signs and whose exact energy is `E`. -/
theorem L1mat_of_exact {a b p0 : ℕ} {E : UPoly} {ks : List ℕ}
    (hperm : ks.Perm (List.range ((a + 1) * (b + 1) - 1))) {L : List Bool}
    (hlen : L.length = (a + 1) * (b + 1) - 1)
    (hsigns : signsOK ((a + 1) * (b + 1)) (runAcc L (steps a b p0 ks) []) = true)
    (hzero : UPoly.allZero (UPoly.add (absSum ((a + 1) * (b + 1)) (runAcc L (steps a b p0 ks) []))
      (UPoly.neg (UPoly.shift p0 E))) = true) {p : ℤ} (hp : (p0 : ℤ) ≤ p) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) = ((UPoly.eval E p : ℤ) : ℝ) := by
  have hx : (0 : ℤ) ≤ p - p0 := sub_nonneg.2 hp
  have htarget : UPoly.eval (UPoly.shift p0 E) (p - p0) = UPoly.eval E p := by
    rw [UPoly.eval_shift, sub_add_cancel]
  rw [L1mat_eq_runAcc a b p0 hperm hlen, sum_abs_eq_absSum hsigns hx, ← htarget]
  have := UPoly.eval_eq_zero_of_allZero hzero (p - p0)
  simp only [UPoly.eval_add, UPoly.eval_neg] at this
  exact_mod_cast (sub_eq_zero.1 (by linarith))

/-- What a successful certificate proves about `ICGGeneral.L1mat 2 p a b`. -/
theorem certify_sound {a b p0 : ℕ} {E : UPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certify a b p0 E ks star others = true) {p : ℤ}
    (hp : (p0 : ℤ) ≤ p) :
    (∀ L ∈ star :: others, L.length = (a + 1) * (b + 1) - 1 ∧
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) = ((UPoly.eval E p : ℤ) : ℝ)) ∧
    (∀ L : List Bool, L.length = (a + 1) * (b + 1) - 1 → L ∉ star :: others →
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) < ((UPoly.eval E p : ℤ) : ℝ)) := by
  unfold certify at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hperm, hall⟩, hbnb⟩ := h
  have hperm' := List.isPerm_iff.1 hperm
  have hx : (0 : ℤ) ≤ p - p0 := sub_nonneg.2 hp
  have htarget : UPoly.eval (UPoly.shift p0 E) (p - p0) = UPoly.eval E p := by
    rw [UPoly.eval_shift, sub_add_cancel]
  refine ⟨fun L hL => ?_, fun L hL hnot => ?_⟩
  · obtain ⟨⟨hlen, hsigns⟩, hzero⟩ := hall L hL
    exact ⟨hlen, L1mat_of_exact hperm' hlen hsigns hzero hp⟩
  · have hsound := bnb_sound _ _ _ _ _ hbnb L hx ((a + 1) * (b + 1))
    have hpath : runCells L ((ks.map fun k => (k, cellTable a b p0 k)).map Prod.fst)
        (List.replicate ((a + 1) * (b + 1) - 1) false) = L := by
      simpa [Function.comp_def] using runCells_perm hperm' hL
    rw [hpath] at hsound
    rcases hsound with hmem | hlt
    · exact absurd hmem hnot
    · rw [L1mat_eq_runAcc a b p0 hperm' hL, ← htarget]
      exact_mod_cast hlt

end Solved.ICG
