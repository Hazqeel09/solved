import Formal.Cert.PackedBB
import Formal.Cert.Table
import Formal.Cert.Sums

/-!
# Packed certificate data for tables of polynomials

The generic half of a packed energy certificate: offset encodings of tables
(`encPoly`, `encTable`), the per-cell data `cellData`, and the step builder `buildP`, with the
lemmas that identify the data with the encodings `bnbP_sound` expects (`cellData_eq`,
`buildP_spec`). A table function `tbl : ℕ → Table` gives each cell its `m` entries, each a list
of at most `D` coefficients; `tabT tbl D` reads them at flat indices `e * D + d`.
-/

namespace Solved.Cert.Packed

open Solved.Cert Solved.Cert.Pack Finset UPoly

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

/-- Coefficient `d` of entry `e` of cell `k`'s table, at flat index `e * D + d`. -/
def tabT (tbl : ℕ → Table) (D : ℕ) (k i : ℕ) : ℤ := coeff ((tbl k).get (i / D)) (i % D)

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

/-! ## The data encode `tabT` -/

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

theorem get_mem (t : Table) {e : ℕ} (he : e < t.length) : t.get e ∈ t := by
  rw [Table.get_eq_getElem _ he]; exact List.getElem_mem he

theorem tabT_flat (tbl : ℕ → Table) (D k : ℕ) {e d : ℕ} (hd : d < D) :
    tabT tbl D k (e * D + d) = coeff ((tbl k).get e) d := by
  rw [tabT, flat_div e hd, flat_mod e hd]

theorem colSum_tabT (tbl : ℕ → Table) {m D k : ℕ} (hlen : (tbl k).length = m) {d : ℕ}
    (hd : d < D) : colSum m D (tabT tbl D k) d = coeff (sumPolys (tbl k)) d := by
  rw [coeff_sumPolys, ← sum_range_get, hlen]
  exact sum_congr rfl fun e _ => tabT_flat tbl D k hd

theorem colSum_min_tabT (tbl : ℕ → Table) {m D k : ℕ} (hlen : (tbl k).length = m) {d : ℕ}
    (hd : d < D) :
    colSum m D (fun i => min (tabT tbl D k i) 0) d =
      coeff (sumPolys (List.map UPoly.negPart (tbl k))) d := by
  rw [coeff_sumPolys, ← sum_range_get, List.length_map, hlen]
  refine sum_congr rfl fun e _ => ?_
  dsimp only
  rw [Table.get_map _ rfl, coeff_negPart, tabT_flat tbl D k hd]

theorem cellData_eq (tbl : ℕ → Table) (w : ℕ) {m D : ℕ} (hD : 0 < D) {k : ℕ}
    (hlen : (tbl k).length = m) :
    cellData w (2 ^ (w - 1)) D k (tbl k) =
      (k, enc w (m * D) (tabT tbl D k), enc w D (colSum m D (tabT tbl D k)),
        enc w D (colSum m D fun i => min (tabT tbl D k i) 0)) := by
  simp only [cellData, encTable_eq w hD, hlen, encPoly_eq]
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_))
  · exact enc_congr fun d hd => (colSum_tabT tbl hlen hd).symm
  · exact enc_congr fun d hd => (colSum_min_tabT tbl hlen hd).symm

theorem sum_absT_tabT (tbl : ℕ → Table) {m D : ℕ} {ks : List ℕ}
    (hlen : ∀ k, (tbl k).length = m) (hlenD : ∀ k ∈ ks, ∀ f ∈ tbl k, f.length ≤ D) :
    ∑ i ∈ range (m * D), absT (tabT tbl D) ks i = (ks.map fun k => absTotal (tbl k)).sum := by
  simp only [absT]
  rw [sum_listSum]
  refine congrArg List.sum (List.map_congr_left fun k hk => ?_)
  rw [sum_range_mul_flat, absTotal, ← sum_range_get, hlen]
  refine sum_congr rfl fun e he => ?_
  rw [← sum_abs_coeff _ (hlenD k hk _ (get_mem _ (by rw [hlen]; exact mem_range.1 he)))]
  exact sum_congr rfl fun d hd => by rw [tabT_flat tbl D k (mem_range.1 hd)]

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

end Solved.Cert.Packed
