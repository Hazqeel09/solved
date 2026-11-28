import Formal.Cert.PackedData
import Formal.ICG.EvenCert
import Formal.ICG.MultiCell

/-!
# The packed energy certificate for a multi-prime order on a region

For an order `s` on a region (`Shape`), cell `kc` contributes to class `e` the bivariate
polynomial `s.cellB (dec e) (dec kc)` in the region coordinates `x, y ≥ 0`; `tblM` lists their
flat coefficients. `certifyM` checks that the claimed maximisers have energy `E(σ₁, σ₂)` exactly,
by coefficient signs, and runs the proved packed search (`bnbP`) with monomial weights `xⁱyʲ`
for every other mask. `certifyM_sound` states the result for every point of the region.
-/

namespace Solved.ICG.Multi

open Solved.Cert Solved.Cert.Pack Solved.Cert.Packed Finset UPoly

variable {k : ℕ}

/-- The flat coefficient table of cell `kc`: one entry per class. -/
def tblM (s : Shape k) (Dx Dy kc : ℕ) : Table :=
  (List.range (size s.a)).map fun e => flat Dx Dy (s.cellB (dec s.a e) (dec s.a kc))

theorem length_tblM (s : Shape k) (Dx Dy kc : ℕ) : (tblM s Dx Dy kc).length = size s.a := by
  simp [tblM]

theorem get_tblM (s : Shape k) (Dx Dy kc : ℕ) {e : ℕ} (he : e < size s.a) :
    (tblM s Dx Dy kc).get e = flat Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) :=
  Table.get_map_range _ _ he

/-- The target `E(σ₁, σ₂)` in the region coordinates. -/
def target (s : Shape k) (E : BPoly) : BPoly :=
  BPoly.subst E s.σ1.c0 s.σ1.c1 s.σ1.c2 s.σ2.c0 s.σ2.c1 s.σ2.c2

/-! ## The tables a mask selects -/

theorem coeff_get_add (s t : Table) (e d : ℕ) :
    coeff ((Table.add s t).get e) d = coeff (s.get e) d + coeff (t.get e) d := by
  induction s generalizing t e with
  | nil => simp [Table.add]
  | cons f s ih =>
    cases t with
    | nil => cases e <;> simp [Table.add]
    | cons g t => cases e <;> simp [Table.add, ih, coeff_add]

/-- The sum of the tables of the cells `L` selects among `ks`. -/
def accT (tbl : ℕ → Table) (L : List Bool) : List ℕ → Table
  | [] => []
  | kc :: ks => if bit L kc then Table.add (tbl kc) (accT tbl L ks) else accT tbl L ks

theorem coeff_accT (tbl : ℕ → Table) (L : List Bool) (ks : List ℕ) (e d : ℕ) :
    coeff ((accT tbl L ks).get e) d =
      (ks.map fun kc => if bit L kc then coeff ((tbl kc).get e) d else 0).sum := by
  induction ks with
  | nil => simp [accT]
  | cons kc ks ih =>
    simp only [accT, List.map_cons, List.sum_cons]
    split_ifs <;> simp [coeff_get_add, ih]

/-! ## Values against monomial weights -/

/-- `∑_{d<D} coeff f d · ω_d`. -/
def valueW (D : ℕ) (ω : ℕ → ℤ) (f : UPoly) : ℤ := ∑ d ∈ range D, coeff f d * ω d

theorem valueW_add (D : ℕ) (ω : ℕ → ℤ) (f g : UPoly) :
    valueW D ω (add f g) = valueW D ω f + valueW D ω g := by
  simp [valueW, coeff_add, add_mul, sum_add_distrib]

theorem valueW_neg (D : ℕ) (ω : ℕ → ℤ) (f : UPoly) : valueW D ω (neg f) = -valueW D ω f := by
  simp [valueW, coeff_neg, sum_neg_distrib]

theorem valueW_signed {D : ℕ} {ω : ℕ → ℤ} (hω : Weights ω) {f : UPoly}
    (h : (allNonneg f || allNonpos f) = true) : valueW D ω (signed f) = |valueW D ω f| := by
  unfold signed
  split_ifs with h₀
  · exact (abs_of_nonneg (show 0 ≤ valueW D ω f from sum_nonneg fun d _ =>
      mul_nonneg (coeff_nonneg_of_allNonneg h₀ d) (hω.nonneg d))).symm
  · simp only [h₀, Bool.false_or] at h
    rw [valueW_neg, abs_of_nonpos (show valueW D ω f ≤ 0 from sum_nonpos fun d _ =>
      mul_nonpos_of_nonpos_of_nonneg (coeff_nonpos_of_allNonpos h d) (hω.nonneg d))]

theorem valueW_sumRange (D : ℕ) (ω : ℕ → ℤ) (n : ℕ) (F : ℕ → UPoly) :
    valueW D ω (sumRange n F) = ∑ i ∈ range n, valueW D ω (F i) := by
  induction n with
  | zero => simp [sumRange, valueW]
  | succ n ih => rw [sumRange, valueW_add, ih, sum_range_succ]

theorem valueW_eq_of_allZero {D : ℕ} {ω : ℕ → ℤ} {f g : UPoly}
    (h : allZero (add f (neg g)) = true) : valueW D ω f = valueW D ω g := by
  unfold valueW
  refine sum_congr rfl fun d _ => ?_
  have := coeff_eq_zero_of_allZero h d
  rw [coeff_add, coeff_neg] at this
  rw [show coeff f d = coeff g d by linarith]

theorem valueW_flat {Dx Dy : ℕ} {P : BPoly} (hP : BPoly.bounded Dx Dy P = true) (x y : ℤ) :
    valueW (Dx * Dy) (monos Dy x y) (flat Dx Dy P) = BPoly.eval P x y :=
  sum_flat Dx Dy P (BPoly.bounded_spec hP).1 (BPoly.bounded_spec hP).2 x y

/-! ## The certificate -/

/-- The packed certificate for the order `s` on its region, with field width `w` and at most
`Dx × Dy` coefficients per polynomial. -/
def certifyM (s : Shape k) (w Dx Dy : ℕ) (E : BPoly) (ks : List ℕ) (star : List Bool)
    (others : List (List Bool)) : Bool :=
  let N := size s.a
  let D := Dx * Dy
  let c := Cfg.of w N D
  let O := 2 ^ (w - 1)
  let tE := flat Dx Dy (target s E)
  let tbl := tblM s Dx Dy
  let tabs := ks.map fun kc => (kc, tbl kc)
  let ss := buildP c.RN c.RD c.RN (encPoly w O D tE)
    (tabs.map fun kt => cellData w O D kt.1 kt.2)
  Nat.blt 0 w && Nat.blt 0 Dx && Nat.blt 0 Dy && ks.isPerm (List.range (N - 1)) &&
    (List.range N).all (fun e => ks.all fun kc =>
      BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc))) &&
    BPoly.bounded Dx Dy (target s E) &&
    decide (4 * (N : ℤ) * (tabs.map fun kt => absTotal kt.2).sum + (tE.map fun c => |c|).sum <
      2 ^ (w - 1)) &&
    (star :: others).all (fun L => L.length == N - 1 && signsOK N (accT tbl L ks) &&
      allZero (add (absSum N (accT tbl L ks)) (neg tE))) &&
    bnbP c ((star :: others).map maskC) c.RN (encPoly w O D tE) ss 0 c.RN c.RD

/-- The energy of mask `L` at a point of the region, in the form of the spectral bridge. -/
def energyAt (s : Shape k) (L : List Bool) (x y : ℤ) : ℤ :=
  ∑ e ∈ range (size s.a), |∑ kc ∈ range (size s.a - 1),
    if bit L kc then BPoly.eval (s.cellB (dec s.a e) (dec s.a kc)) x y else 0|

theorem inner_eq {s : Shape k} {Dx Dy : ℕ} {ks : List ℕ} (hperm : ks.Perm (List.range (size s.a - 1)))
    (hb : ∀ e < size s.a, ∀ kc ∈ ks, BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) = true)
    (L : List Bool) {e : ℕ} (he : e < size s.a) (x y : ℤ) :
    ∑ d ∈ range (Dx * Dy), chosenT (tabT (tblM s Dx Dy) (Dx * Dy)) L ks (e * (Dx * Dy) + d) *
        monos Dy x y d =
      ∑ kc ∈ range (size s.a - 1),
        if bit L kc then BPoly.eval (s.cellB (dec s.a e) (dec s.a kc)) x y else 0 := by
  simp only [chosenT]
  rw [sum_listSum_mul]
  have : ∀ kc ∈ ks, (∑ d ∈ range (Dx * Dy), (if bit L kc then tabT (tblM s Dx Dy) (Dx * Dy) kc
      (e * (Dx * Dy) + d) else 0) * monos Dy x y d) =
      if bit L kc then BPoly.eval (s.cellB (dec s.a e) (dec s.a kc)) x y else 0 := by
    intro kc hkc
    split_ifs
    · rw [← valueW_flat (hb e he kc hkc), valueW]
      refine sum_congr rfl fun d hd => ?_
      rw [tabT_flat _ _ kc (mem_range.1 hd), get_tblM s Dx Dy kc he]
    · simp
  rw [List.map_congr_left this, (hperm.map _).sum_eq, sum_map_range]

/-- The value of entry `e` of the table a mask accumulates. -/
theorem valueW_accT {s : Shape k} {Dx Dy : ℕ} {ks : List ℕ}
    (hperm : ks.Perm (List.range (size s.a - 1)))
    (hb : ∀ e < size s.a, ∀ kc ∈ ks, BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) = true)
    (L : List Bool) {e : ℕ} (he : e < size s.a) (x y : ℤ) :
    valueW (Dx * Dy) (monos Dy x y) ((accT (tblM s Dx Dy) L ks).get e) =
      ∑ kc ∈ range (size s.a - 1),
        if bit L kc then BPoly.eval (s.cellB (dec s.a e) (dec s.a kc)) x y else 0 := by
  rw [← inner_eq hperm hb L he x y, valueW]
  refine sum_congr rfl fun d hd => ?_
  rw [coeff_accT, chosenT]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun kc _ => ?_)
  rw [tabT_flat _ _ kc (mem_range.1 hd)]

/-- The energy of a mask is the sum of the absolute values of its accumulated entries. -/
theorem energyAt_eq {s : Shape k} {Dx Dy : ℕ} {ks : List ℕ}
    (hperm : ks.Perm (List.range (size s.a - 1)))
    (hb : ∀ e < size s.a, ∀ kc ∈ ks, BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) = true)
    (L : List Bool) (x y : ℤ) :
    energyAt s L x y = ∑ e ∈ range (size s.a),
      |valueW (Dx * Dy) (monos Dy x y) ((accT (tblM s Dx Dy) L ks).get e)| :=
  sum_congr rfl fun e he => by rw [valueW_accT hperm hb L (mem_range.1 he)]

/-- What a successful certificate proves, at every point `x, y ≥ 0` of the region. -/
theorem certifyM_sound {s : Shape k} {w Dx Dy : ℕ} {E : BPoly} {ks : List ℕ} {star : List Bool}
    {others : List (List Bool)} (h : certifyM s w Dx Dy E ks star others = true) {x y : ℤ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (∀ L ∈ star :: others, L.length = size s.a - 1 ∧
      energyAt s L x y = BPoly.eval (target s E) x y) ∧
    (∀ L : List Bool, L.length = size s.a - 1 → L ∉ star :: others →
      energyAt s L x y < BPoly.eval (target s E) x y) := by
  unfold certifyM at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.blt_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hw, hDx⟩, hDy⟩, hperm⟩, hb⟩, htb⟩, hsz⟩, hall⟩, hbnb⟩ := h
  have hperm' := List.isPerm_iff.1 hperm
  have hb' : ∀ e < size s.a, ∀ kc ∈ ks,
      BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) = true :=
    fun e he kc hkc => hb e (List.mem_range.2 he) kc hkc
  have hω : Weights (monos Dy x y) := ⟨monos_nonneg Dy hx hy, by rw [monos_zero]; norm_num⟩
  have hD : 0 < Dx * Dy := Nat.mul_pos hDx hDy
  have htarget : valueW (Dx * Dy) (monos Dy x y) (flat Dx Dy (target s E)) =
      BPoly.eval (target s E) x y := valueW_flat htb x y
  refine ⟨fun L hL => ?_, fun L hL hnot => ?_⟩
  · -- the claimed maximisers, by coefficient signs
    obtain ⟨⟨hlen, hsigns⟩, hzero⟩ := hall L hL
    refine ⟨hlen, ?_⟩
    rw [energyAt_eq hperm' hb', ← htarget, ← valueW_eq_of_allZero hzero, absSum, valueW_sumRange]
    refine sum_congr rfl fun e he => ?_
    rw [valueW_signed hω (List.all_eq_true.1 hsigns e (List.mem_range.2 (mem_range.1 he)))]
  · -- every other mask, by the packed search
    have hlenk : ∀ kc ∈ ks, ∀ f ∈ tblM s Dx Dy kc, f.length ≤ Dx * Dy := by
      intro kc _ f hf
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hf
      rw [length_flat]
    have hc := Cfg.of_OK (m := size s.a) hw (size_pos s.a) hD
    have hsize : SizeOK (Cfg.of w (size s.a) (Dx * Dy))
        (absT (tabT (tblM s Dx Dy) (Dx * Dy)) ks) (coeff (flat Dx Dy (target s E))) := by
      unfold SizeOK
      simp only [Cfg.of]
      rw [sum_absT_tabT (tblM s Dx Dy) (length_tblM s Dx Dy) hlenk,
        sum_abs_coeff _ (le_of_eq (length_flat _ _ _))]
      simpa [List.map_map, Function.comp_def] using hsz
    have hleafC : encPoly w (2 ^ (w - 1)) (Dx * Dy) (flat Dx Dy (target s E)) =
        Pack.enc (Cfg.of w (size s.a) (Dx * Dy)).w (Cfg.of w (size s.a) (Dx * Dy)).D
          (coeff (flat Dx Dy (target s E))) := encPoly_eq w _ _
    obtain ⟨hok, -, -⟩ := buildP_spec hc hsize (fun kc => cellData w (2 ^ (w - 1)) (Dx * Dy) kc
      (tblM s Dx Dy kc)) (fun kc => cellData_eq (tblM s Dx Dy) w hD (length_tblM s Dx Dy kc))
      hleafC ks fun i _ => le_rfl
    have hroot : ∀ i < (Cfg.of w (size s.a) (Dx * Dy)).m * (Cfg.of w (size s.a) (Dx * Dy)).D,
        |(fun _ => (0 : ℤ)) i| + absT (tabT (tblM s Dx Dy) (Dx * Dy)) ks i ≤
          absT (tabT (tblM s Dx Dy) (Dx * Dy)) ks i := by simp
    have hleafS : (Cfg.of w (size s.a) (Dx * Dy)).RN =
        Pack.enc (Cfg.of w (size s.a) (Dx * Dy)).w
          ((Cfg.of w (size s.a) (Dx * Dy)).m * (Cfg.of w (size s.a) (Dx * Dy)).D)
          (sumT (tabT (tblM s Dx Dy) (Dx * Dy)) []) := by
      rw [hc.hRN, ← enc_zero]; exact enc_congr fun _ _ => by simp
    have hacc : Pack.enc (Cfg.of w (size s.a) (Dx * Dy)).w
        ((Cfg.of w (size s.a) (Dx * Dy)).m * (Cfg.of w (size s.a) (Dx * Dy)).D) (fun _ => 0) =
        (Cfg.of w (size s.a) (Dx * Dy)).RN := by rw [hc.hRN, enc_zero]
    have haccS : Pack.enc (Cfg.of w (size s.a) (Dx * Dy)).w (Cfg.of w (size s.a) (Dx * Dy)).D
        (colSum (Cfg.of w (size s.a) (Dx * Dy)).m (Cfg.of w (size s.a) (Dx * Dy)).D
          fun _ => 0) = (Cfg.of w (size s.a) (Dx * Dy)).RD := by
      rw [hc.hRD, ← enc_zero]; exact enc_congr fun _ _ => by simp [colSum]
    have hbb := hbnb
    rw [List.map_map] at hbb
    have hsound := bnbP_sound hc hsize hleafS hleafC ks _ hok 0 (fun _ => 0) hroot
      (by rw [hacc, haccS]; simpa [Function.comp_def] using hbb) L hω
    rcases hsound with hmem | hlt
    · exfalso
      rw [runMask_perm hperm' L, ← List.map_cons] at hmem
      obtain ⟨L', hL', hEq⟩ := List.mem_map.1 hmem
      have hlenL' := (hall L' hL').1.1
      rw [maskC_eq, hlenL'] at hEq
      exact hnot (maskOf_inj hL hlenL' hEq.symm ▸ hL')
    · simp only [Cfg.of] at hlt
      unfold energyAt
      rw [← htarget]
      unfold energy at hlt
      refine lt_of_eq_of_lt ?_ hlt
      refine sum_congr rfl fun e he => ?_
      simp only [zero_add]
      rw [inner_eq hperm' hb' L (mem_range.1 he) x y]

end Solved.ICG.Multi
