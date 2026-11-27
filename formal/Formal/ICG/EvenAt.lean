import Formal.ICG.EvenGraph

/-!
# The energy certificate at one prime

For a fixed prime `p` the entries of `L1mat 2 p a b` are integers. `certifyAt` reuses the
branch and bound of `Solved.Cert.bnb` with constant tables (`cellTableAt`): a bound that is
positive for all `x ≥ 0` is in particular positive at `x = 0`, which is all that is used.
It covers primes below a family's `p₀`, where the maximisers differ, such as `n = 2^3 · 3`.
-/

namespace Solved.ICG

open Solved.Cert Finset

/-- The contributions of cell `k` at the prime `p`, as constant polynomials. -/
def cellTableAt (a b p k : ℕ) : Table :=
  (List.range ((a + 1) * (b + 1))).map fun e => [UPoly.eval (cellP a b k e) p]

/-- The decision steps over all cells below the top one, in order. -/
def stepsAt (a b p : ℕ) : List Step :=
  build ((List.range ((a + 1) * (b + 1) - 1)).map fun k => (k, cellTableAt a b p k))

/-- `∑_{e < m} |tₑ(0)|` by recursion, for the kernel. -/
def absSumAt (t : Table) : ℕ → ℤ
  | 0 => 0
  | e + 1 => absSumAt t e + |UPoly.eval (t.get e) 0|

theorem absSumAt_eq (t : Table) (m : ℕ) :
    absSumAt t m = ∑ e ∈ range m, |UPoly.eval (t.get e) 0| := by
  induction m with
  | zero => rfl
  | succ m ih => rw [absSumAt, ih, sum_range_succ]

/-- The certificate for `2^a p^b` at one prime `p`: each mask in `star :: others` (masks of
length `(a+1)(b+1) - 1`) has energy `E`, and every other mask has smaller energy. -/
def certifyAt (a b p : ℕ) (E : ℤ) (star : List Bool) (others : List (List Bool)) : Bool :=
  let m := (a + 1) * (b + 1)
  let ss := stepsAt a b p
  (star :: others).all (fun L => L.length == m - 1 && absSumAt (runAcc L ss []) m == E) &&
    bnb [E] (star :: others) ss (List.replicate (m - 1) false) []

theorem eval_runAcc_stepsAt (a b p : ℕ) {L : List Bool} (hL : L.length = (a + 1) * (b + 1) - 1)
    {e : ℕ} (he : e < (a + 1) * (b + 1)) :
    UPoly.eval ((runAcc L (stepsAt a b p) []).get e) 0 =
      UPoly.eval (entryP a b L (e / (b + 1)) (e % (b + 1))) p := by
  have hm : (a + 1) * (b + 1) = ((a + 1) * (b + 1) - 1) + 1 :=
    (Nat.sub_add_cancel (Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b))).symm
  rw [stepsAt, eval_runAcc_build L _ _ (List.Perm.refl _), eval_entryP_flat, hm, sum_range_succ,
    bit_of_length_le hL.le, ← hm]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  refine sum_congr rfl fun k _ => ?_
  rw [cellTableAt, Table.get_map_range _ _ he]
  simp

theorem L1mat_eq_runAccAt (a b p : ℕ) {L : List Bool} (hL : L.length = (a + 1) * (b + 1) - 1) :
    ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) =
      ((∑ e ∈ range ((a + 1) * (b + 1)),
        |UPoly.eval ((runAcc L (stepsAt a b p) []).get e) 0| : ℤ) : ℝ) := by
  rw [show (p : ℝ) = ((p : ℤ) : ℝ) by push_cast; rfl, L1mat_flat]
  push_cast
  refine sum_congr rfl fun e he => ?_
  rw [eval_runAcc_stepsAt a b p hL (mem_range.1 he)]

/-- What a successful certificate at one prime proves about `ICGGeneral.L1mat 2 p a b`. -/
theorem certifyAt_sound {a b p : ℕ} {E : ℤ} {star : List Bool} {others : List (List Bool)}
    (h : certifyAt a b p E star others = true) :
    (∀ L ∈ star :: others, L.length = (a + 1) * (b + 1) - 1 ∧
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) = (E : ℝ)) ∧
    (∀ L : List Bool, L.length = (a + 1) * (b + 1) - 1 → L ∉ star :: others →
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) < (E : ℝ)) := by
  unfold certifyAt at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hall, hbnb⟩ := h
  refine ⟨fun L hL => ?_, fun L hL hnot => ?_⟩
  · obtain ⟨hlen, hE⟩ := hall L hL
    refine ⟨hlen, ?_⟩
    rw [L1mat_eq_runAccAt a b p hlen, ← absSumAt_eq, hE]
  · have hsound := bnb_sound _ _ _ _ _ hbnb L (le_refl 0) ((a + 1) * (b + 1))
    have hpath : runCells L (((List.range ((a + 1) * (b + 1) - 1)).map fun k =>
        (k, cellTableAt a b p k)).map Prod.fst)
        (List.replicate ((a + 1) * (b + 1) - 1) false) = L := by
      simpa [Function.comp_def] using runCells_perm (List.Perm.refl _) hL
    rw [hpath] at hsound
    rcases hsound with hmem | hlt
    · exact absurd hmem hnot
    · rw [L1mat_eq_runAccAt a b p hL]
      have : UPoly.eval [E] 0 = E := by simp
      rw [this] at hlt
      exact_mod_cast hlt

/-- What a successful certificate at one odd prime proves about integral circulant graphs. -/
theorem energy_le_of_certifyAt {a b p : ℕ} {E : ℤ} {star : List Bool}
    {others : List (List Bool)} (h : certifyAt a b p E star others = true) (hp : p.Prime)
    (hp2 : p ≠ 2) {S : Finset ℕ} (hS : S ⊆ (2 ^ a * p ^ b).properDivisors) :
    ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) ≤
        (E : ℝ) ∧
      (ICGBridge.energy (ICGBridge.icgAdj (2 ^ a * p ^ b) S) (ICGBridge.icgAdj_isHermitian _ _) =
          (E : ℝ) ↔ S ∈ (star :: others).map (divsOfMask a b p)) := by
  obtain ⟨hmax, hlt⟩ := certifyAt_sound h
  rw [energy_eq_L1mat hp hp2 hS]
  have hlen := length_maskOfDivs a b p S
  by_cases hmem : maskOfDivs a b p S ∈ star :: others
  · have heq := (hmax _ hmem).2
    refine ⟨heq.le, ⟨fun _ => ?_, fun _ => heq⟩⟩
    exact List.mem_map.2 ⟨_, hmem, divsOfMask_maskOfDivs hp hS⟩
  · have hl := hlt _ hlen hmem
    refine ⟨hl.le, ⟨fun he => absurd he hl.ne, fun hS' => ?_⟩⟩
    obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hS'
    exact absurd (by rw [maskOfDivs_divsOfMask hp hp2 (hmax L hL).1]; exact hL) hmem

end Solved.ICG
