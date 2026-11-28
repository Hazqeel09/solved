import Formal.ICG.MultiGraph

/-!
# Certificates for regions where the maximiser depends on the primes

On some regions no single divisor set is maximal everywhere: for `2p²q` with `p > q` the winner
changes with the ratio of the primes. `certifyMax` then proves that each candidate `j` has the
exact energy `E_j`, and that every other mask has energy below some `E_j`:

* the proved packed search runs against one candidate's energy `E_{i₀}`, allowing the
  candidates and a list of residual masks;
* each residual mask is checked directly: `G` times its coefficientwise absolute energy bound
  is below a convex mixture `∑ⱼ mⱼ E_j` with `∑ⱼ mⱼ = G`, so its energy is below some `E_j`.
-/

namespace Solved.ICG.Multi

open Solved.Cert Solved.Cert.Pack Solved.Cert.Packed Finset UPoly

variable {k : ℕ}

/-! ## Mixtures and absolute bounds -/

/-- `∑ⱼ mⱼ tⱼ`. -/
def mixP : List ℕ → List UPoly → UPoly
  | c :: m, t :: ts => add (scale c t) (mixP m ts)
  | _, _ => []

theorem valueW_mixP (D : ℕ) (ω : ℕ → ℤ) :
    ∀ (m : List ℕ) (ts : List UPoly),
      valueW D ω (mixP m ts) = ((m.zip ts).map fun ct => (ct.1 : ℤ) * valueW D ω ct.2).sum
  | c :: m, t :: ts => by
    rw [mixP, valueW_add, valueW_mixP D ω m ts]
    simp [valueW, coeff_scale, mul_assoc, mul_sum]
  | [], _ => by simp [mixP, valueW]
  | _ :: _, [] => by simp [mixP, valueW]

/-- `∑_{e<N} absC tₑ`. -/
def absBound (N : ℕ) (t : Table) : UPoly := sumRange N fun e => absC (t.get e)

theorem coeff_absC (f : UPoly) (d : ℕ) : coeff (absC f) d = |coeff f d| := by
  induction f generalizing d with
  | nil => simp [absC]
  | cons a f ih =>
    cases d with
    | zero => rfl
    | succ d => exact ih d

theorem abs_valueW_le {D : ℕ} {ω : ℕ → ℤ} (hω : Weights ω) (f : UPoly) :
    |valueW D ω f| ≤ valueW D ω (absC f) := by
  unfold valueW
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_of_nonneg (hω.nonneg d), coeff_absC]

theorem valueW_pos_of_posCert {D : ℕ} (hD : 0 < D) {ω : ℕ → ℤ} (hω : Weights ω) {f : UPoly}
    (h : posCert f = true) : 0 < valueW D ω f := by
  cases f with
  | nil => simp [posCert] at h
  | cons c cs =>
    simp only [posCert, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    rw [valueW, sum_range_succ']
    refine add_pos_of_nonneg_of_pos (sum_nonneg fun d _ => ?_) (mul_pos h.1 hω.pos)
    exact mul_nonneg (coeff_nonneg_of_allNonneg h.2 d) (hω.nonneg _)

/-! ## The certificate -/

/-- Candidates `cands` with energies `Es` (as polynomials in `p, q`), the search target `i₀`,
and residual masks with their mixtures. -/
def certifyMax (s : Shape k) (w Dx Dy G : ℕ) (Es : List BPoly) (i0 : ℕ) (ks : List ℕ)
    (cands : List (List Bool)) (resid : List (List Bool × List ℕ)) : Bool :=
  let N := size s.a
  let D := Dx * Dy
  let c := Cfg.of w N D
  let O := 2 ^ (w - 1)
  let tEs := Es.map fun E => flat Dx Dy (target s E)
  let t0 := tEs.getD i0 []
  let tbl := tblM s Dx Dy
  let tabs := ks.map fun kc => (kc, tbl kc)
  let ss := buildP c.RN c.RD c.RN (encPoly w O D t0)
    (tabs.map fun kt => cellData w O D kt.1 kt.2)
  Nat.blt 0 w && Nat.blt 0 Dx && Nat.blt 0 Dy && Nat.blt 0 G && Nat.blt i0 Es.length &&
    cands.length == Es.length && ks.isPerm (List.range (N - 1)) &&
    (List.range N).all (fun e => ks.all fun kc =>
      BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc))) &&
    Es.all (fun E => BPoly.bounded Dx Dy (target s E)) &&
    decide (4 * (N : ℤ) * (tabs.map fun kt => absTotal kt.2).sum + (t0.map fun c => |c|).sum <
      2 ^ (w - 1)) &&
    (cands.zip tEs).all (fun Lt => Lt.1.length == N - 1 && signsOK N (accT tbl Lt.1 ks) &&
      allZero (add (absSum N (accT tbl Lt.1 ks)) (neg Lt.2))) &&
    resid.all (fun Rm => Rm.1.length == N - 1 && Rm.2.length == Es.length && Rm.2.sum == G &&
      posCert (add (mixP Rm.2 tEs) (neg (scale G (absBound N (accT tbl Rm.1 ks)))))) &&
    bnbP c ((cands ++ resid.map Prod.fst).map maskC) c.RN (encPoly w O D t0) ss 0 c.RN c.RD

/-- A mask whose `G`-fold absolute bound is below a mixture with weights summing to `G` is
below one of the mixed energies. -/
theorem lt_of_mixture {e : ℤ} {G : ℕ} (vals : List ℤ) (m : List ℕ) (hlen : m.length = vals.length)
    (hsum : m.sum = G) (h : (G : ℤ) * e < ((m.zip vals).map fun cv => (cv.1 : ℤ) * cv.2).sum) :
    ∃ v ∈ vals, e < v := by
  by_contra hne
  push Not at hne
  have key : ∀ (m : List ℕ) (vals : List ℤ), m.length = vals.length → (∀ v ∈ vals, v ≤ e) →
      ((m.zip vals).map fun cv => (cv.1 : ℤ) * cv.2).sum ≤ (m.sum : ℤ) * e := by
    intro m
    induction m with
    | nil => intro vals _ _; simp
    | cons c m ih =>
      intro vals hl hv
      cases vals with
      | nil => simp at hl
      | cons v vals =>
        simp only [List.length_cons] at hl
        have h1 := ih vals (by omega) fun u hu => hv u (List.mem_cons_of_mem _ hu)
        have h2 : (c : ℤ) * v ≤ c * e := mul_le_mul_of_nonneg_left (hv v (by simp)) (by positivity)
        calc ((((c :: m).zip (v :: vals)).map fun cv => (cv.1 : ℤ) * cv.2).sum)
            = (c : ℤ) * v + ((m.zip vals).map fun cv => (cv.1 : ℤ) * cv.2).sum := by simp
          _ ≤ (c : ℤ) * e + (m.sum : ℤ) * e := add_le_add h2 h1
          _ = (((c :: m).sum : ℕ) : ℤ) * e := by push_cast [List.sum_cons]; ring
  have := key m vals hlen hne
  rw [hsum] at this
  linarith

/-- What a successful certificate proves at every point `x, y ≥ 0` of the region: each
candidate has its own exact energy, and every other mask is below one of them. -/
theorem certifyMax_sound {s : Shape k} {w Dx Dy G : ℕ} {Es : List BPoly} {i0 : ℕ}
    {ks : List ℕ} {cands : List (List Bool)} {resid : List (List Bool × List ℕ)}
    (h : certifyMax s w Dx Dy G Es i0 ks cands resid = true) {x y : ℤ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cands.length = Es.length ∧
    (∀ LE ∈ cands.zip Es, LE.1.length = size s.a - 1 ∧
      energyAt s LE.1 x y = BPoly.eval (target s LE.2) x y) ∧
    (∀ L : List Bool, L.length = size s.a - 1 → L ∉ cands →
      ∃ E ∈ Es, energyAt s L x y < BPoly.eval (target s E) x y) := by
  unfold certifyMax at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Nat.blt_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hw, hDx⟩, hDy⟩, hG⟩, hi0⟩, hclen⟩, hperm⟩, hb⟩, htb⟩, hsz⟩, hall⟩, hres⟩,
    hbnb⟩ := h
  have hperm' := List.isPerm_iff.1 hperm
  have hb' : ∀ e < size s.a, ∀ kc ∈ ks,
      BPoly.bounded Dx Dy (s.cellB (dec s.a e) (dec s.a kc)) = true :=
    fun e he kc hkc => hb e (List.mem_range.2 he) kc hkc
  have hω : Weights (monos Dy x y) := ⟨monos_nonneg Dy hx hy, by rw [monos_zero]; norm_num⟩
  have hD : 0 < Dx * Dy := Nat.mul_pos hDx hDy
  have hval : ∀ E ∈ Es, valueW (Dx * Dy) (monos Dy x y) (flat Dx Dy (target s E)) =
      BPoly.eval (target s E) x y := fun E hE => valueW_flat (htb E hE) x y
  -- exact energies of the candidates
  have hexact : ∀ LE ∈ cands.zip Es, LE.1.length = size s.a - 1 ∧
      energyAt s LE.1 x y = BPoly.eval (target s LE.2) x y := by
    intro LE hLE
    have hmem : (LE.1, flat Dx Dy (target s LE.2)) ∈
        cands.zip (Es.map fun E => flat Dx Dy (target s E)) := by
      rw [List.zip_map_right]
      exact List.mem_map.2 ⟨LE, hLE, rfl⟩
    obtain ⟨⟨hlen, hsigns⟩, hzero⟩ := hall _ hmem
    refine ⟨hlen, ?_⟩
    rw [energyAt_eq hperm' hb', ← hval LE.2 (List.of_mem_zip hLE).2,
      ← valueW_eq_of_allZero hzero, absSum, valueW_sumRange]
    refine sum_congr rfl fun e he => ?_
    rw [valueW_signed hω (List.all_eq_true.1 hsigns e (List.mem_range.2 (mem_range.1 he)))]
  refine ⟨hclen, hexact, fun L hL hnot => ?_⟩
  by_cases hR : L ∈ resid.map Prod.fst
  · -- a residual mask, by its mixture
    obtain ⟨⟨R, m⟩, hRm, rfl⟩ := List.mem_map.1 hR
    obtain ⟨⟨⟨-, hmlen⟩, hmsum⟩, hpos⟩ := hres _ hRm
    have hp := valueW_pos_of_posCert hD hω hpos
    rw [valueW_add, valueW_neg, valueW_mixP] at hp
    have hbound : (G : ℤ) * energyAt s R x y ≤
        valueW (Dx * Dy) (monos Dy x y) (scale G (absBound (size s.a) (accT (tblM s Dx Dy) R ks))) := by
      rw [valueW, show (∑ d ∈ range (Dx * Dy), coeff (scale G _) d * monos Dy x y d) =
        (G : ℤ) * valueW (Dx * Dy) (monos Dy x y) (absBound (size s.a) (accT (tblM s Dx Dy) R ks)) by
          simp [valueW, coeff_scale, mul_sum, mul_assoc]]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rw [energyAt_eq hperm' hb', absBound, valueW_sumRange]
      exact sum_le_sum fun e _ => abs_valueW_le hω _
    have hlt' : (G : ℤ) * energyAt s R x y <
        ((m.zip (Es.map fun E => flat Dx Dy (target s E))).map
          fun ct => (ct.1 : ℤ) * valueW (Dx * Dy) (monos Dy x y) ct.2).sum := by
      linarith
    have hlt : (G : ℤ) * energyAt s R x y <
        ((m.zip ((Es.map fun E => flat Dx Dy (target s E)).map
          (valueW (Dx * Dy) (monos Dy x y)))).map fun cv => (cv.1 : ℤ) * cv.2).sum := by
      simpa [List.zip_map_right, List.map_map, Function.comp_def] using hlt'
    obtain ⟨v, hv, hev⟩ := lt_of_mixture _ m (by simpa using hmlen) hmsum hlt
    obtain ⟨E, hE, rfl⟩ := List.mem_map.1 (by simpa [List.map_map, Function.comp_def] using hv)
    exact ⟨E, hE, by rwa [hval E hE] at hev⟩
  · -- every other mask, by the search against `E_{i₀}`
    have hlenk : ∀ kc ∈ ks, ∀ f ∈ tblM s Dx Dy kc, f.length ≤ Dx * Dy := by
      intro kc _ f hf
      obtain ⟨e, -, rfl⟩ := List.mem_map.1 hf
      rw [length_flat]
    have hc := Cfg.of_OK (m := size s.a) hw (size_pos s.a) hD
    set t0 := (Es.map fun E => flat Dx Dy (target s E)).getD i0 [] with ht0
    have hE0 : t0 = flat Dx Dy (target s (Es.get ⟨i0, hi0⟩)) := by
      rw [ht0, List.getD_eq_getElem _ _ (by simpa using hi0)]
      simp
    have hsize : SizeOK (Cfg.of w (size s.a) (Dx * Dy))
        (absT (tabT (tblM s Dx Dy) (Dx * Dy)) ks) (coeff t0) := by
      unfold SizeOK
      simp only [Cfg.of]
      rw [sum_absT_tabT (tblM s Dx Dy) (length_tblM s Dx Dy) hlenk,
        sum_abs_coeff _ (by rw [hE0, length_flat])]
      simpa [List.map_map, Function.comp_def] using hsz
    have hleafC : encPoly w (2 ^ (w - 1)) (Dx * Dy) t0 =
        Pack.enc (Cfg.of w (size s.a) (Dx * Dy)).w (Cfg.of w (size s.a) (Dx * Dy)).D (coeff t0) :=
      encPoly_eq w _ _
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
      rw [runMask_perm hperm' L] at hmem
      have hmem' : maskOf (size s.a - 1) L ∈ (cands ++ resid.map Prod.fst).map maskC := by
        simpa [List.map_append, List.map_map, Function.comp_def] using hmem
      obtain ⟨L', hL', hEq⟩ := List.mem_map.1 hmem'
      have hlenL' : L'.length = size s.a - 1 := by
        rcases List.mem_append.1 hL' with hc' | hr'
        · obtain ⟨E, hE⟩ : ∃ E, (L', E) ∈ cands.zip Es := by
            obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hc'
            have hj' : j < (cands.zip Es).length := by rw [List.length_zip, ← hclen, min_self]; exact hj
            have hm := List.getElem_mem hj'
            rw [List.getElem_zip] at hm
            exact ⟨_, hm⟩
          exact (hexact _ hE).1
        · obtain ⟨⟨R, m⟩, hRm, rfl⟩ := List.mem_map.1 hr'
          exact (hres _ hRm).1.1.1
      rw [maskC_eq, hlenL'] at hEq
      have hLL' := maskOf_inj hL hlenL' hEq.symm
      rcases List.mem_append.1 hL' with hc' | hr'
      · exact hnot (hLL' ▸ hc')
      · exact hR (hLL' ▸ hr')
    · refine ⟨Es.get ⟨i0, hi0⟩, List.get_mem _ _, ?_⟩
      simp only [Cfg.of] at hlt
      have htv : ∑ d ∈ range (Dx * Dy), coeff t0 d * monos Dy x y d =
          BPoly.eval (target s (Es.get ⟨i0, hi0⟩)) x y := by
        rw [← valueW_flat (htb _ (List.get_mem _ _)) x y, hE0]; rfl
      unfold energyAt
      rw [← htv]
      unfold energy at hlt
      refine lt_of_eq_of_lt ?_ hlt
      refine sum_congr rfl fun e he => ?_
      simp only [zero_add]
      rw [inner_eq hperm' hb' L (mem_range.1 he) x y]

end Solved.ICG.Multi
