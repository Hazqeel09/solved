import Formal.Cert.PackedBB
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

open Solved.Cert Solved.Cert.Pack Solved.Cert.Packed Finset

/-! ## Coefficients -/

/-- Coefficient `d` of a polynomial (zero past the end). -/
def coeff : UPoly → ℕ → ℤ
  | [], _ => 0
  | c :: _, 0 => c
  | _ :: cs, d + 1 => coeff cs d

@[simp] theorem coeff_nil (d : ℕ) : coeff [] d = 0 := by cases d <;> rfl
@[simp] theorem coeff_cons_zero (c : ℤ) (cs : UPoly) : coeff (c :: cs) 0 = c := rfl
@[simp] theorem coeff_cons_succ (c : ℤ) (cs : UPoly) (d : ℕ) :
    coeff (c :: cs) (d + 1) = coeff cs d := rfl

theorem coeff_add (f g : UPoly) (d : ℕ) : coeff (UPoly.add f g) d = coeff f d + coeff g d := by
  induction f generalizing g d with
  | nil => simp [UPoly.add]
  | cons a f ih =>
    cases g with
    | nil => cases d <;> simp [UPoly.add]
    | cons b g => cases d <;> simp [UPoly.add, ih]

theorem coeff_negPart (f : UPoly) (d : ℕ) : coeff (UPoly.negPart f) d = min (coeff f d) 0 := by
  induction f generalizing d with
  | nil => simp [UPoly.negPart]
  | cons a f ih =>
    cases d with
    | zero => rfl
    | succ d => exact ih d

theorem eval_eq_sum_coeff (f : UPoly) {D : ℕ} (h : f.length ≤ D) (x : ℤ) :
    UPoly.eval f x = ∑ d ∈ range D, coeff f d * x ^ d := by
  induction f generalizing D with
  | nil => simp
  | cons a f ih =>
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by simp at h; omega⟩
    rw [UPoly.eval_cons, sum_range_succ', ih (by simpa using h), mul_sum]
    simp only [coeff_cons_succ, coeff_cons_zero, pow_zero, mul_one]
    rw [add_comm]
    congr 1
    exact sum_congr rfl fun d _ => by ring

theorem sum_abs_coeff (f : UPoly) {D : ℕ} (h : f.length ≤ D) :
    ∑ d ∈ range D, |coeff f d| = (f.map fun c => |c|).sum := by
  induction f generalizing D with
  | nil => simp
  | cons a f ih =>
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by simp at h; omega⟩
    rw [sum_range_succ']
    simp only [coeff_cons_succ, coeff_cons_zero]
    rw [ih (by simpa using h)]
    simp [add_comm]

/-! ## Sums over tables and cell lists -/

theorem sum_range_get {M : Type*} [AddCommMonoid M] (t : Table) (g : UPoly → M) :
    ∑ e ∈ range t.length, g (t.get e) = (t.map g).sum := by
  induction t with
  | nil => simp
  | cons f t ih =>
    rw [List.length_cons, sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [Table.get_cons_succ, Table.get_cons_zero, ih]

theorem sum_listSum_mul (s : Finset ℕ) (l : List ℕ) (F : ℕ → ℕ → ℤ) (g : ℕ → ℤ) :
    ∑ i ∈ s, (l.map fun k => F k i).sum * g i = (l.map fun k => ∑ i ∈ s, F k i * g i).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simp [add_mul, sum_add_distrib, ih]

theorem sum_listSum {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (l : List ℕ)
    (F : ℕ → ℕ → M) :
    ∑ i ∈ s, (l.map fun k => F k i).sum = (l.map fun k => ∑ i ∈ s, F k i).sum := by
  induction l with
  | nil => simp
  | cons k l ih => simp [sum_add_distrib, ih]

/-! ## Certificate data -/

/-- Offset encoding of the first `D` coefficients, for the kernel. -/
def encPoly (w O : ℕ) : ℕ → UPoly → ℕ
  | 0, _ => 0
  | D + 1, [] => O + 2 ^ w * encPoly w O D []
  | D + 1, c :: cs => (c + (O : ℤ)).toNat + 2 ^ w * encPoly w O D cs

/-- Offset encoding of a table, `D` coefficients per entry, for the kernel. -/
def encTable (w O D : ℕ) : Table → ℕ
  | [] => 0
  | f :: fs => encPoly w O D f + 2 ^ (w * D) * encTable w O D fs

/-- The sum of a list of polynomials. -/
def sumPolys : List UPoly → UPoly
  | [] => []
  | f :: fs => UPoly.add f (sumPolys fs)

/-- `∑ |coefficients|` of a table. -/
def absTotal (t : Table) : ℤ := (List.map (fun f : UPoly => (List.map (fun c => |c|) f).sum) t).sum

/-- Coefficient `d` of the shifted contribution of cell `k` to entry `e`, at `e * D + d`. -/
def cellT (a b p0 D : ℕ) (k i : ℕ) : ℤ := coeff ((cellTable a b p0 k).get (i / D)) (i % D)

/-- The packed per-cell data: cell, table, column sums, column sums of negative parts. -/
def cellData (w O D : ℕ) (k : ℕ) (t : Table) : ℕ × ℕ × ℕ × ℕ :=
  (k, encTable w O D t, encPoly w O D (sumPolys t),
    encPoly w O D (sumPolys (List.map UPoly.negPart t)))

/-- `S` of the first step, `leafS` without steps. -/
def headS (leafS : ℕ) : List PStep → ℕ
  | [] => leafS
  | st :: _ => st.s

/-- `target + ∑ₑ lo` of the first step, `leafC` without steps. -/
def headC (leafC : ℕ) : List PStep → ℕ
  | [] => leafC
  | st :: _ => st.c

/-- The steps of the packed search, with `S` and `target + ∑ₑ lo` accumulated from the end. -/
def buildP (RN RD leafS leafC : ℕ) : List (ℕ × ℕ × ℕ × ℕ) → List PStep
  | [] => []
  | (k, tab, tsum, los) :: r =>
    let ss := buildP RN RD leafS leafC r
    { cell := k, tab := tab, tsum := tsum, s := headS leafS ss + tab - RN,
      c := headC leafC ss + los - RD } :: ss

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

theorem toNat_two_pow (n : ℕ) : ((2 : ℤ) ^ n).toNat = 2 ^ n := by
  rw [show (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast]

theorem enc_congr {w n : ℕ} {f g : ℕ → ℤ} (h : ∀ i < n, f i = g i) : enc w n f = enc w n g :=
  pack_congr fun i hi => by rw [h i hi]

theorem encPoly_eq (w D : ℕ) (f : UPoly) : encPoly w (2 ^ (w - 1)) D f = enc w D (coeff f) := by
  induction D generalizing f with
  | zero => simp [encPoly, enc]
  | succ D ih =>
    cases f with
    | nil =>
      rw [encPoly, ih, enc, enc, pack_succ]
      simp only [coeff_nil, zero_add, toNat_two_pow]
    | cons c cs =>
      rw [encPoly, ih, enc, enc, pack_succ]
      push_cast
      rfl

theorem encTable_eq (w : ℕ) {D : ℕ} (hD : 0 < D) (t : Table) :
    encTable w (2 ^ (w - 1)) D t = enc w (t.length * D) fun i => coeff (t.get (i / D)) (i % D) := by
  induction t with
  | nil => simp [encTable, enc]
  | cons f t ih =>
    rw [encTable, ih, encPoly_eq, List.length_cons, show (t.length + 1) * D = D + t.length * D by
      ring, enc, enc, enc, pack_split]
    congr 1
    · refine pack_congr fun i hi => ?_
      rw [Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]; rfl
    · congr 1
      refine pack_congr fun i _ => ?_
      rw [Nat.add_div_left _ hD, Nat.add_mod_left]
      rfl

theorem coeff_sumPolys (t : Table) (d : ℕ) :
    coeff (sumPolys t) d = (t.map fun f => coeff f d).sum := by
  induction t with
  | nil => simp [sumPolys]
  | cons f t ih => simp [sumPolys, coeff_add, ih]

theorem length_cellTable (a b p0 k : ℕ) : (cellTable a b p0 k).length = (a + 1) * (b + 1) := by
  simp [cellTable]

theorem cellT_flat (a b p0 D k : ℕ) {e d : ℕ} (hd : d < D) :
    cellT a b p0 D k (e * D + d) = coeff ((cellTable a b p0 k).get e) d := by
  rw [cellT, flat_div e hd, flat_mod e hd]

theorem colSum_cellT (a b p0 D k : ℕ) {d : ℕ} (hd : d < D) :
    colSum ((a + 1) * (b + 1)) D (cellT a b p0 D k) d = coeff (sumPolys (cellTable a b p0 k)) d := by
  rw [coeff_sumPolys, ← sum_range_get, length_cellTable]
  exact sum_congr rfl fun e _ => cellT_flat a b p0 D k hd

theorem colSum_min_cellT (a b p0 D k : ℕ) {d : ℕ} (hd : d < D) :
    colSum ((a + 1) * (b + 1)) D (fun i => min (cellT a b p0 D k i) 0) d =
      coeff (sumPolys (List.map UPoly.negPart (cellTable a b p0 k))) d := by
  rw [coeff_sumPolys, ← sum_range_get, List.length_map, length_cellTable]
  refine sum_congr rfl fun e _ => ?_
  dsimp only
  rw [Table.get_map _ rfl, coeff_negPart, cellT_flat a b p0 D k hd]

theorem cellData_eq (a b p0 w : ℕ) {D : ℕ} (hD : 0 < D) (k : ℕ) :
    cellData w (2 ^ (w - 1)) D k (cellTable a b p0 k) =
      (k, enc w ((a + 1) * (b + 1) * D) (cellT a b p0 D k),
        enc w D (colSum ((a + 1) * (b + 1)) D (cellT a b p0 D k)),
        enc w D (colSum ((a + 1) * (b + 1)) D fun i => min (cellT a b p0 D k i) 0)) := by
  simp only [cellData, encTable_eq w hD, length_cellTable, encPoly_eq]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · exact enc_congr fun d hd => (colSum_cellT a b p0 D k hd).symm
  · exact enc_congr fun d hd => (colSum_min_cellT a b p0 D k hd).symm

/-! ## The steps -/

theorem enc_zero (w n : ℕ) : enc w n (fun _ => 0) = rep w n (2 ^ (w - 1)) := by
  simp only [enc, zero_add, toNat_two_pow, rep]

theorem buildP_spec {c : Cfg} (hc : c.OK) {T : ℕ → ℕ → ℤ} {t Bf : ℕ → ℤ}
    (hsize : SizeOK c Bf t) (data : ℕ → ℕ × ℕ × ℕ × ℕ)
    (hdata : ∀ k, data k = (k, enc c.w (c.m * c.D) (T k), enc c.w c.D (colSum c.m c.D (T k)),
      enc c.w c.D (colSum c.m c.D fun i => min (T k i) 0)))
    {leafC : ℕ} (hleafC : leafC = enc c.w c.D t) :
    ∀ rem : List ℕ, (∀ i < c.m * c.D, absT T rem i ≤ Bf i) →
      StepsOK c T t (buildP c.RN c.RD c.RN leafC (rem.map data)) rem ∧
      headS c.RN (buildP c.RN c.RD c.RN leafC (rem.map data)) =
        enc c.w (c.m * c.D) (sumT T rem) ∧
      headC leafC (buildP c.RN c.RD c.RN leafC (rem.map data)) =
        enc c.w c.D (fun d => t d + colSum c.m c.D (loT T rem) d) := by
  intro rem
  induction rem with
  | nil =>
    intro _
    refine ⟨trivial, ?_, ?_⟩
    · simp only [List.map_nil, buildP, headS, hc.hRN, ← enc_zero]
      exact enc_congr fun _ _ => by simp
    · simp only [List.map_nil, buildP, headC, hleafC]
      exact enc_congr fun d _ => by simp [colSum]
  | cons k rem ih =>
    intro hrem
    have hrem' : ∀ i < c.m * c.D, absT T rem i ≤ Bf i := fun i hi => by
      have := hrem i hi; rw [absT_cons] at this; linarith [abs_nonneg (T k i)]
    obtain ⟨hok, hS, hC⟩ := ih hrem'
    have hBf0 : ∀ i < c.m * c.D, 0 ≤ Bf i := fun i hi => (absT_nonneg T _ i).trans (hrem i hi)
    have hinv : ∀ rem', (∀ i < c.m * c.D, absT T rem' i ≤ Bf i) →
        ∀ i < c.m * c.D, |(fun _ => (0 : ℤ)) i| + absT T rem' i ≤ Bf i := fun rem' h i hi => by
      simpa using h i hi
    obtain ⟨-, hSk, -, -, hCk, -, -, -⟩ := fits_of_inv hc.hm hsize (hinv _ hrem)
    obtain ⟨-, hSr, -, -, hCr, -, -, -⟩ := fits_of_inv hc.hm hsize (hinv _ hrem')
    have hTkle : ∀ i < c.m * c.D, |T k i| ≤ Bf i := fun i hi => by
      have := hrem i hi; rw [absT_cons] at this; linarith [absT_nonneg T rem i]
    have hTk := fits_of_le hc.hm hsize hBf0 hTkle
    have hlok := fits_colSum_of_le hc.hm hsize hBf0 (f := fun i => min (T k i) 0)
      fun i hi => by
        refine le_trans ?_ (hTkle i hi)
        rcases le_total (T k i) 0 with h | h
        · rw [min_eq_left h]
        · rw [min_eq_right h]; simp
    have hs : headS c.RN (buildP c.RN c.RD c.RN leafC (rem.map data)) +
        enc c.w (c.m * c.D) (T k) - c.RN = enc c.w (c.m * c.D) (sumT T (k :: rem)) := by
      rw [hS]
      refine sub_eq_enc hSk ?_
      rw [hc.hRN]; push_cast
      rw [cast_enc hSr, cast_enc hTk, cast_rep]
      rw [show sumT T (k :: rem) = fun i => T k i + sumT T rem i from funext (sumT_cons T k rem),
        packZ_add]
      push_cast; ring
    have hcs : headC leafC (buildP c.RN c.RD c.RN leafC (rem.map data)) +
        enc c.w c.D (colSum c.m c.D fun i => min (T k i) 0) - c.RD =
        enc c.w c.D (fun d => t d + colSum c.m c.D (loT T (k :: rem)) d) := by
      rw [hC]
      refine sub_eq_enc hCk ?_
      rw [hc.hRD]; push_cast
      rw [cast_enc hCr, cast_enc hlok, cast_rep]
      have : (fun d => t d + colSum c.m c.D (loT T (k :: rem)) d) =
          fun d => (t d + colSum c.m c.D (loT T rem) d) +
            colSum c.m c.D (fun i => min (T k i) 0) d := by
        funext d; simp only [colSum, loT_cons, sum_add_distrib]; ring
      rw [this]
      simp only [packZ_add]
      push_cast; ring
    simp only [List.map_cons, hdata k, buildP]
    exact ⟨⟨rfl, rfl, rfl, hs, hcs, hok⟩, hs, hcs⟩

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

theorem sum_absT_cellT (a b p0 D : ℕ) {ks : List ℕ}
    (hlen : ∀ k ∈ ks, ∀ f ∈ cellTable a b p0 k, f.length ≤ D) :
    ∑ i ∈ range ((a + 1) * (b + 1) * D), absT (cellT a b p0 D) ks i =
      (ks.map fun k => absTotal (cellTable a b p0 k)).sum := by
  simp only [absT]
  rw [sum_listSum]
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  rw [sum_range_mul_flat, absTotal, ← sum_range_get, length_cellTable]
  refine sum_congr rfl fun e he => ?_
  rw [← sum_abs_coeff _ (hlen k hk _ (mem_cellTable a b p0 k (mem_range.1 he)))]
  exact sum_congr rfl fun d hd => by rw [cellT_flat a b p0 D k (mem_range.1 hd)]

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
    rw [sum_absT_cellT a b p0 D hlenk, sum_abs_coeff _ htlen]
    simpa [List.map_map, Function.comp_def] using hsz
  have hleafC : encPoly w (2 ^ (w - 1)) D (UPoly.shift p0 E) =
      enc (Cfg.of w ((a + 1) * (b + 1)) D).w (Cfg.of w ((a + 1) * (b + 1)) D).D
        (coeff (UPoly.shift p0 E)) := encPoly_eq w D _
  obtain ⟨hok, -, -⟩ := buildP_spec hc hsize (fun k => cellData w (2 ^ (w - 1)) D k
    (cellTable a b p0 k)) (fun k => cellData_eq a b p0 w hD k) hleafC ks fun i _ => le_rfl
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
