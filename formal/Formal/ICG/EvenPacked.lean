import Formal.Cert.PackedData
import Formal.ICG.EvenCert

/-!
# The packed energy certificate for orders `2^a p^b`

`certifyP` proves the same statement as `certify` (`certifyP_sound`), but runs the search on
packed coefficient tables (`Solved.Cert.Packed.bnbP`), which the kernel evaluates with a fixed
number of GMP operations per node.

Cell `k`'s table is `cellT a b p0 D k`: coefficient `d` of the shifted contribution of cell `k`
to entry `e`, at flat index `e * D + d`. Maximisers are checked exactly as in `certify`.
-/

namespace Solved.ICG

open Solved.Cert Solved.Cert.Pack Solved.Cert.Packed Finset UPoly

/-! ## Certificate data -/

/-- Coefficient `d` of the shifted contribution of cell `k` to entry `e`, at `e * D + d`. -/
abbrev cellT (a b p0 D : ℕ) : ℕ → ℕ → ℤ := tabT (cellTable a b p0) D

/-- The packed certificate for `2^a p^b` from `p ≥ p₀`, with field width `w` and `D`
coefficients per polynomial. -/
def certifyP (a b p0 w D : ℕ) (E : UPoly) (ks : List ℕ) (star : List Bool)
    (others : List (List Bool)) : Bool :=
  let m := (a + 1) * (b + 1)
  let c := Cfg.of w m D
  let O := 2 ^ (w - 1)
  let tP := UPoly.shift p0 E
  let tabs := ks.map fun k => (k, cellTable a b p0 k)
  let ss := buildP c.RN c.RD c.RN (encPoly w O D tP)
    (tabs.map fun kt => cellData w O D kt.1 kt.2)
  let ls := steps a b p0 ks
  Nat.blt 0 w && Nat.blt 0 D && ks.isPerm (List.range (m - 1)) &&
    tabs.all (fun kt => kt.2.all fun f => Nat.ble f.length D) && Nat.ble tP.length D &&
    decide (4 * (m : ℤ) * (tabs.map fun kt => absTotal kt.2).sum + (tP.map fun c => |c|).sum <
      2 ^ (w - 1)) &&
    (star :: others).all (fun L => L.length == m - 1 && signsOK m (runAcc L ls []) &&
      UPoly.allZero (UPoly.add (absSum m (runAcc L ls [])) (UPoly.neg tP))) &&
    bnbP c ((star :: others).map maskC) c.RN (encPoly w O D tP) ss 0 c.RN c.RD

/-! ## The data encode `cellT` -/

theorem length_cellTable (a b p0 k : ℕ) : (cellTable a b p0 k).length = (a + 1) * (b + 1) := by
  simp [cellTable]

theorem cellT_flat (a b p0 D k : ℕ) {e d : ℕ} (hd : d < D) :
    cellT a b p0 D k (e * D + d) = coeff ((cellTable a b p0 k).get e) d :=
  tabT_flat _ D k hd

/-! ## Energies -/

theorem mem_cellTable (a b p0 k : ℕ) {e : ℕ} (he : e < (a + 1) * (b + 1)) :
    (cellTable a b p0 k).get e ∈ cellTable a b p0 k := by
  rw [cellTable, Table.get_map_range _ _ he]
  exact List.mem_map.2 ⟨e, List.mem_range.2 he, rfl⟩

theorem energy_cellT (a b p0 D : ℕ) {ks : List ℕ}
    (hlen : ∀ k ∈ ks, ∀ f ∈ cellTable a b p0 k, f.length ≤ D) (L : List Bool) (x : ℤ) :
    energy ((a + 1) * (b + 1)) D (fun i => 0 + chosenT (cellT a b p0 D) L ks i) (fun d => x ^ d) =
      ∑ e ∈ range ((a + 1) * (b + 1)), |UPoly.eval ((runAcc L (steps a b p0 ks) []).get e) x| := by
  unfold energy
  refine sum_congr rfl fun e he => ?_
  congr 1
  rw [steps, eval_runAcc, chosen_build, List.map_map]
  simp only [Table.get_nil, UPoly.eval_nil, zero_add, chosenT, Function.comp_def]
  rw [sum_listSum_mul]
  congr 1
  refine List.map_congr_left fun k hk => ?_
  split_ifs
  · rw [eval_eq_sum_coeff _ (hlen k hk _ (mem_cellTable a b p0 k (mem_range.1 he)))]
    exact sum_congr rfl fun d hd => by rw [cellT_flat a b p0 D k (mem_range.1 hd)]
  · simp

/-! ## Soundness -/

/-- What a successful packed certificate proves about `ICGGeneral.L1mat 2 p a b`: the same as
`certify_sound`. -/
theorem certifyP_sound {a b p0 w D : ℕ} {E : UPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certifyP a b p0 w D E ks star others = true) {p : ℤ}
    (hp : (p0 : ℤ) ≤ p) :
    (∀ L ∈ star :: others, L.length = (a + 1) * (b + 1) - 1 ∧
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) = ((UPoly.eval E p : ℤ) : ℝ)) ∧
    (∀ L : List Bool, L.length = (a + 1) * (b + 1) - 1 → L ∉ star :: others →
      ICGGeneral.L1mat 2 (p : ℝ) a b (ind b L) < ((UPoly.eval E p : ℤ) : ℝ)) := by
  unfold certifyP at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.blt_eq, Nat.ble_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hw, hD⟩, hperm⟩, hlen⟩, htlen⟩, hsz⟩, hall⟩, hbnb⟩ := h
  have hperm' := List.isPerm_iff.1 hperm
  have hm : 0 < (a + 1) * (b + 1) := Nat.mul_pos (Nat.succ_pos a) (Nat.succ_pos b)
  have hc := Cfg.of_OK (m := (a + 1) * (b + 1)) hw hm hD
  have hx : (0 : ℤ) ≤ p - p0 := sub_nonneg.2 hp
  have htarget : UPoly.eval (UPoly.shift p0 E) (p - p0) = UPoly.eval E p := by
    rw [UPoly.eval_shift, sub_add_cancel]
  refine ⟨fun L hL => ?_, fun L hL hnot => ?_⟩
  · obtain ⟨⟨hlenL, hsigns⟩, hzero⟩ := hall L hL
    exact ⟨hlenL, L1mat_of_exact hperm' hlenL hsigns hzero hp⟩
  -- the search
  have hlenk : ∀ k ∈ ks, ∀ f ∈ cellTable a b p0 k, f.length ≤ D := fun k hk f hf =>
    hlen (k, cellTable a b p0 k) (List.mem_map.2 ⟨k, hk, rfl⟩) f hf
  have hsize : SizeOK (Cfg.of w ((a + 1) * (b + 1)) D) (absT (cellT a b p0 D) ks)
      (coeff (UPoly.shift p0 E)) := by
    unfold SizeOK
    simp only [Cfg.of]
    rw [sum_absT_tabT (cellTable a b p0) (length_cellTable a b p0) hlenk, sum_abs_coeff _ htlen]
    simpa [List.map_map, Function.comp_def] using hsz
  have hleafC : encPoly w (2 ^ (w - 1)) D (UPoly.shift p0 E) =
      enc (Cfg.of w ((a + 1) * (b + 1)) D).w (Cfg.of w ((a + 1) * (b + 1)) D).D
        (coeff (UPoly.shift p0 E)) := encPoly_eq w D _
  obtain ⟨hok, -, -⟩ := buildP_spec hc hsize (fun k => cellData w (2 ^ (w - 1)) D k
    (cellTable a b p0 k)) (fun k => cellData_eq (cellTable a b p0) w hD (length_cellTable a b p0 k))
    hleafC ks fun i _ => le_rfl
  have hroot : ∀ i < (Cfg.of w ((a + 1) * (b + 1)) D).m * (Cfg.of w ((a + 1) * (b + 1)) D).D,
      |(fun _ => (0 : ℤ)) i| + absT (cellT a b p0 D) ks i ≤ absT (cellT a b p0 D) ks i := by
    simp
  have hleafS : (Cfg.of w ((a + 1) * (b + 1)) D).RN =
      enc (Cfg.of w ((a + 1) * (b + 1)) D).w
        ((Cfg.of w ((a + 1) * (b + 1)) D).m * (Cfg.of w ((a + 1) * (b + 1)) D).D)
        (sumT (cellT a b p0 D) []) := by
    rw [hc.hRN, ← enc_zero]; exact enc_congr fun _ _ => by simp
  have hacc : enc (Cfg.of w ((a + 1) * (b + 1)) D).w
      ((Cfg.of w ((a + 1) * (b + 1)) D).m * (Cfg.of w ((a + 1) * (b + 1)) D).D) (fun _ => 0) =
      (Cfg.of w ((a + 1) * (b + 1)) D).RN := by rw [hc.hRN, enc_zero]
  have haccS : enc (Cfg.of w ((a + 1) * (b + 1)) D).w (Cfg.of w ((a + 1) * (b + 1)) D).D
      (colSum (Cfg.of w ((a + 1) * (b + 1)) D).m (Cfg.of w ((a + 1) * (b + 1)) D).D
        fun _ => 0) = (Cfg.of w ((a + 1) * (b + 1)) D).RD := by
    rw [hc.hRD, ← enc_zero]; exact enc_congr fun _ _ => by simp [colSum]
  have hb := hbnb
  rw [List.map_map] at hb
  have hsound := bnbP_sound hc hsize hleafS hleafC ks _ hok 0 (fun _ => 0) hroot
    (by rw [hacc, haccS]; simpa [Function.comp_def] using hb) L (weights_pow hx)
  rcases hsound with hmem | hlt
  · exfalso
    rw [runMask_perm hperm' L, ← List.map_cons] at hmem
    obtain ⟨L', hL', hEq⟩ := List.mem_map.1 hmem
    have hlenL' := (hall L' hL').1.1
    rw [maskC_eq, hlenL'] at hEq
    exact hnot (maskOf_inj hL hlenL' hEq.symm ▸ hL')
  · rw [L1mat_eq_runAcc a b p0 hperm' hL, ← htarget]
    have h1 := energy_cellT a b p0 D hlenk L (p - p0)
    have h2 : ∑ d ∈ range D, coeff (UPoly.shift p0 E) d * (p - p0) ^ d =
        UPoly.eval (UPoly.shift p0 E) (p - p0) := (eval_eq_sum_coeff _ htlen _).symm
    simp only [Cfg.of] at hlt
    rw [h1, h2] at hlt
    exact_mod_cast hlt

end Solved.ICG
