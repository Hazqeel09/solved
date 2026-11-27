import Formal.Cert.Mask
import Formal.Cert.Pack
import Formal.Cert.Sums

/-!
# Branch and bound on packed coefficient tables

Cell `k` contributes the integer table `T k`: `m` polynomials with `D` coefficients each,
coefficient `d` of polynomial `e` at flat index `e * D + d`. The energy of a mask at `x` is
`∑ₑ |∑_d (∑_{k ∈ L} T k (eD+d)) ω_d|` for monomial values `ω_d ≥ 0` with `ω_0 > 0`, such as
`ω_d = xᵈ` at `x ≥ 0` (one variable) or `xⁱyʲ` at `x, y ≥ 0` (two variables).

At a node with accumulated table `a` and undecided cells `rem`, every completion's coefficient
lies between `a + lo` and `a + hi`, where `lo` and `hi` sum the negative and positive parts of
the contributions of `rem`; `hi - lo` is their absolute sum and `hi + lo = S` their sum. Hence
its absolute value is at most `max (a + hi) (-(a + lo)) = -a - lo + max (2a + S) 0`, and the
energy is at most `∑_d βd ω_d` with `βd = ∑ₑ (-a - lo + max (2a + S) 0)` (`energy_le`).

`nodeTest` decides `target - β` has a positive constant and nonnegative coefficients using a
fixed number of operations on packed numbers (`Solved.Cert.Pack`): the accumulated table, the
sum of its blocks and the precomputed `S` and `target + ∑ₑ lo` are offset-encoded in one natural
number each. `bnbP` is the search, and `bnbP_sound` its correctness, under one global size
condition that keeps every field inside its `w` bits.
-/

namespace Solved.Cert.Packed

open Finset Pack

/-! ## Semantics -/

/-- `∑_{e<m} |∑_{d<D} f(eD+d) ω_d|` for monomial values `ω`, such as `ω_d = xᵈ` or
`ω_{iD'+j} = xⁱ yʲ`. -/
def energy (m D : ℕ) (f : ℕ → ℤ) (ω : ℕ → ℤ) : ℤ :=
  ∑ e ∈ range m, |∑ d ∈ range D, f (e * D + d) * ω d|

/-- Monomial values at a point of the region: all nonnegative, the constant one positive. -/
structure Weights (ω : ℕ → ℤ) : Prop where
  nonneg : ∀ d, 0 ≤ ω d
  pos : 0 < ω 0

theorem weights_pow {x : ℤ} (hx : 0 ≤ x) : Weights fun d => x ^ d :=
  ⟨fun d => pow_nonneg hx d, by simp⟩

/-- `∑_{k ∈ ks} T k i`. -/
def sumT (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : ℤ := (ks.map fun k => T k i).sum

/-- `∑_{k ∈ ks} min (T k i) 0`. -/
def loT (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : ℤ := (ks.map fun k => min (T k i) 0).sum

/-- `∑_{k ∈ ks} |T k i|`. -/
def absT (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : ℤ := (ks.map fun k => |T k i|).sum

/-- The contributions the mask `L` selects among `ks`. -/
def chosenT (T : ℕ → ℕ → ℤ) (L : List Bool) (ks : List ℕ) (i : ℕ) : ℤ :=
  (ks.map fun k => if bit L k then T k i else 0).sum

@[simp] theorem sumT_nil (T : ℕ → ℕ → ℤ) (i : ℕ) : sumT T [] i = 0 := rfl
@[simp] theorem loT_nil (T : ℕ → ℕ → ℤ) (i : ℕ) : loT T [] i = 0 := rfl
@[simp] theorem absT_nil (T : ℕ → ℕ → ℤ) (i : ℕ) : absT T [] i = 0 := rfl
@[simp] theorem chosenT_nil (T : ℕ → ℕ → ℤ) (L : List Bool) (i : ℕ) : chosenT T L [] i = 0 := rfl

theorem sumT_cons (T : ℕ → ℕ → ℤ) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    sumT T (k :: ks) i = T k i + sumT T ks i := by simp [sumT]
theorem loT_cons (T : ℕ → ℕ → ℤ) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    loT T (k :: ks) i = min (T k i) 0 + loT T ks i := by simp [loT]
theorem absT_cons (T : ℕ → ℕ → ℤ) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    absT T (k :: ks) i = |T k i| + absT T ks i := by simp [absT]
theorem chosenT_cons (T : ℕ → ℕ → ℤ) (L : List Bool) (k : ℕ) (ks : List ℕ) (i : ℕ) :
    chosenT T L (k :: ks) i = (if bit L k then T k i else 0) + chosenT T L ks i := by
  simp [chosenT]

theorem absT_nonneg (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : 0 ≤ absT T ks i := by
  induction ks with
  | nil => simp
  | cons k ks ih => rw [absT_cons]; exact add_nonneg (abs_nonneg _) ih

theorem abs_sumT_le (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : |sumT T ks i| ≤ absT T ks i := by
  induction ks with
  | nil => simp
  | cons k ks ih => rw [sumT_cons, absT_cons]; exact (abs_add_le _ _).trans (add_le_add le_rfl ih)

theorem abs_loT_le (T : ℕ → ℕ → ℤ) (ks : List ℕ) (i : ℕ) : |loT T ks i| ≤ absT T ks i := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [loT_cons, absT_cons]
    refine (abs_add_le _ _).trans (add_le_add ?_ ih)
    rcases le_total (T k i) 0 with h | h
    · rw [min_eq_left h]
    · rw [min_eq_right h]; simp

/-- Completions lie between the sums of negative and of positive parts. -/
theorem chosenT_bounds (T : ℕ → ℕ → ℤ) (L : List Bool) (ks : List ℕ) (i : ℕ) :
    loT T ks i ≤ chosenT T L ks i ∧ chosenT T L ks i ≤ sumT T ks i - loT T ks i := by
  induction ks with
  | nil => simp
  | cons k ks ih =>
    rw [loT_cons, chosenT_cons, sumT_cons]
    obtain ⟨h₁, h₂⟩ := ih
    constructor
    · split_ifs
      · linarith [min_le_left (T k i) 0]
      · linarith [min_le_right (T k i) 0]
    · split_ifs
      · linarith [min_le_right (T k i) 0]
      · linarith [min_le_left (T k i) 0]

theorem abs_add_le_field {a c lo S : ℤ} (h₁ : lo ≤ c) (h₂ : c ≤ S - lo) :
    |a + c| ≤ -a - lo + max (2 * a + S) 0 := by
  have hm₁ := le_max_left (2 * a + S) 0
  have hm₂ := le_max_right (2 * a + S) 0
  rw [abs_le]; constructor <;> linarith

/-- Coefficient `d` of the node bound. -/
def beta (m D : ℕ) (a S lo : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ e ∈ range m, (-a (e * D + d) - lo (e * D + d) + max (2 * a (e * D + d) + S (e * D + d)) 0)

theorem energy_le (m D : ℕ) (T : ℕ → ℕ → ℤ) (L : List Bool) (ks : List ℕ) (a : ℕ → ℤ)
    {ω : ℕ → ℤ} (hω : Weights ω) :
    energy m D (fun i => a i + chosenT T L ks i) ω ≤
      ∑ d ∈ range D, beta m D a (sumT T ks) (loT T ks) d * ω d := by
  unfold energy beta
  simp only [sum_mul]
  rw [sum_comm]
  refine sum_le_sum fun e _ => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun d _ => ?_)
  rw [abs_mul, abs_of_nonneg (hω.nonneg d)]
  obtain ⟨h₁, h₂⟩ := chosenT_bounds T L ks (e * D + d)
  exact mul_le_mul_of_nonneg_right (abs_add_le_field h₁ h₂) (hω.nonneg d)

theorem sum_pos_of_coeffs {D : ℕ} (hD : 0 < D) {z : ℕ → ℤ} (h0 : 0 < z 0)
    (h : ∀ d < D, 0 ≤ z d) {ω : ℕ → ℤ} (hω : Weights ω) : 0 < ∑ d ∈ range D, z d * ω d := by
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
  rw [sum_range_succ']
  refine add_pos_of_nonneg_of_pos (sum_nonneg fun d hd => ?_) (mul_pos h0 hω.pos)
  exact mul_nonneg (h (d + 1) (by simpa using hd)) (hω.nonneg _)

/-! ## The packed node test -/

/-- Field width `w`, `m` entries of `D` coefficients, the packed offset constants
`RN = rep w (mD) 2^{w-1}`, `RD = rep w D 2^{w-1}`, and `R = spread w D m` for block sums. -/
structure Cfg where
  w : ℕ
  m : ℕ
  D : ℕ
  RN : ℕ
  RD : ℕ
  R : ℕ

/-- The configuration with its constants computed by recursion. -/
def Cfg.of (w m D : ℕ) : Cfg :=
  ⟨w, m, D, repC w (2 ^ (w - 1)) (m * D), repC w (2 ^ (w - 1)) D, spreadC w D m⟩

/-- A configuration whose constants are the offset patterns. -/
structure Cfg.OK (c : Cfg) : Prop where
  hw : 0 < c.w
  hm : 0 < c.m
  hD : 0 < c.D
  hRN : c.RN = rep c.w (c.m * c.D) (2 ^ (c.w - 1))
  hRD : c.RD = rep c.w c.D (2 ^ (c.w - 1))
  hR : c.R = spread c.w c.D c.m

theorem Cfg.of_OK {w m D : ℕ} (hw : 0 < w) (hm : 0 < m) (hD : 0 < D) : (Cfg.of w m D).OK :=
  ⟨hw, hm, hD, repC_eq _ _ _, repC_eq _ _ _, spreadC_eq _ _ _⟩

/-- Packed decision of `target - β > 0` by coefficients, from `s = enc S`,
`cc = enc (target + ∑ₑ lo)`, `acc = enc a` and `accSum = enc (∑ₑ a)`. -/
def nodeTest (c : Cfg) (s cc acc accSum : ℕ) : Bool :=
  let X := 2 * acc + s - 2 * c.RN
  let H := blockSum c.w c.D c.m c.R (posPack c.w c.RN X)
  let Z := cc + accSum - c.RD - H
  Nat.beq (Z &&& c.RD) c.RD && Nat.blt (2 ^ (c.w - 1)) (Z % 2 ^ c.w)

/-- `∑ₑ max (2 a + S) 0` at coefficient `d`. -/
def hPos (m D : ℕ) (a S : ℕ → ℤ) (d : ℕ) : ℤ :=
  ∑ e ∈ range m, max (2 * a (e * D + d) + S (e * D + d)) 0

theorem field_posPart {w : ℕ} {x : ℤ} (h : |x| < 2 ^ (w - 1)) :
    (if 2 ^ (w - 1) ≤ (x + 2 ^ (w - 1)).toNat then (x + 2 ^ (w - 1)).toNat - 2 ^ (w - 1) else 0) =
      (max x 0).toNat := by
  have := abs_lt.1 h
  have hnn : 0 ≤ x + 2 ^ (w - 1) := by linarith
  have hc : ((x + 2 ^ (w - 1)).toNat : ℤ) = x + 2 ^ (w - 1) := Int.toNat_of_nonneg hnn
  split_ifs with hle
  · have hx : 0 ≤ x := by
      have : ((2 ^ (w - 1) : ℕ) : ℤ) ≤ ((x + 2 ^ (w - 1)).toNat : ℤ) := by exact_mod_cast hle
      push_cast at this; linarith
    rw [max_eq_left hx]
    have : (((x + 2 ^ (w - 1)).toNat - 2 ^ (w - 1) : ℕ) : ℤ) = x := by
      rw [Nat.cast_sub hle, hc]; push_cast; ring
    omega
  · have hx : x < 0 := by
      have : ¬ ((2 ^ (w - 1) : ℕ) : ℤ) ≤ ((x + 2 ^ (w - 1)).toNat : ℤ) := by exact_mod_cast hle
      push_cast at this; linarith
    rw [max_eq_right hx.le]; rfl

theorem nodeTest_spec {c : Cfg} (hc : c.OK) {a S C A : ℕ → ℤ}
    (ha : Fits c.w (c.m * c.D) a) (hS : Fits c.w (c.m * c.D) S)
    (hX : Fits c.w (c.m * c.D) fun i => 2 * a i + S i)
    (hC : Fits c.w c.D C) (hA : Fits c.w c.D A) (hCA : Fits c.w c.D fun d => C d + A d)
    (hZ : Fits c.w c.D fun d => C d + A d - hPos c.m c.D a S d)
    {F : ℕ} (hXF : ∀ i < c.m * c.D, |2 * a i + S i| ≤ F) (hmF : c.m * F < 2 ^ c.w)
    (htest : nodeTest c (enc c.w (c.m * c.D) S) (enc c.w c.D C) (enc c.w (c.m * c.D) a)
      (enc c.w c.D A) = true) :
    (∀ d < c.D, 0 ≤ C d + A d - hPos c.m c.D a S d) ∧ 0 < C 0 + A 0 - hPos c.m c.D a S 0 := by
  obtain ⟨hw, hm, hD, hRN, hRD, hR⟩ := hc
  have hOw : 2 ^ (c.w - 1) < 2 ^ c.w := Nat.pow_lt_pow_right (by norm_num) (by omega)
  -- the packed `2a + S`
  have hXe : 2 * enc c.w (c.m * c.D) a + enc c.w (c.m * c.D) S - 2 * c.RN =
      enc c.w (c.m * c.D) (fun i => 2 * a i + S i) := by
    refine sub_eq_enc hX ?_
    rw [hRN]; push_cast
    rw [cast_enc ha, cast_enc hS, cast_rep, packZ_add, packZ_mul_left]
    push_cast; ring
  -- its fieldwise positive part and the block sums
  have hPf : ∀ i < c.m * c.D, (max (2 * a i + S i) 0).toNat ≤ F := by
    intro i hi
    have h1 := hXF i hi
    have : ((max (2 * a i + S i) 0).toNat : ℤ) ≤ F := by
      rw [Int.toNat_of_nonneg (le_max_right _ _)]
      exact max_le ((le_abs_self _).trans h1) (by positivity)
    exact_mod_cast this
  have hH : blockSum c.w c.D c.m c.R
      (posPack c.w c.RN (enc c.w (c.m * c.D) fun i => 2 * a i + S i)) =
      pack c.w c.D fun d =>
        ∑ e ∈ range c.m, (max (2 * a (e * c.D + d) + S (e * c.D + d)) 0).toNat := by
    rw [hRN, enc, posPack_spec hw (enc_fields_lt hw hX), hR, ← blockSum_spec hm hPf hmF]
    congr 1
    exact pack_congr fun i hi => field_posPart (hX i hi)
  -- the packed `C + A - h`
  have hCAe : enc c.w c.D C + enc c.w c.D A - c.RD = enc c.w c.D fun d => C d + A d := by
    refine sub_eq_enc hCA ?_
    rw [hRD]; push_cast
    rw [cast_enc hC, cast_enc hA, cast_rep, packZ_add]
    push_cast; ring
  have hZe : enc c.w c.D (fun d => C d + A d) -
      pack c.w c.D (fun d =>
        ∑ e ∈ range c.m, (max (2 * a (e * c.D + d) + S (e * c.D + d)) 0).toNat) =
      enc c.w c.D fun d => C d + A d - hPos c.m c.D a S d := by
    refine sub_eq_enc hZ ?_
    rw [cast_enc hCA, cast_pack, packZ_sub]
    have : packZ c.w c.D (fun d => ((∑ e ∈ range c.m,
        (max (2 * a (e * c.D + d) + S (e * c.D + d)) 0).toNat : ℕ) : ℤ)) =
        packZ c.w c.D (hPos c.m c.D a S) := by
      refine packZ_congr fun d _ => ?_
      push_cast
      exact sum_congr rfl fun e _ => Int.toNat_of_nonneg (le_max_right _ _)
    rw [this, packZ_add]; ring
  -- decode the test
  unfold nodeTest at htest
  simp only [hXe, hH, hCAe, hZe, Bool.and_eq_true, Nat.beq_eq, Nat.blt_eq] at htest
  obtain ⟨hguard, hlow⟩ := htest
  have hZf := enc_fields_lt hw hZ
  have hdec : ∀ d < c.D, 2 ^ (c.w - 1) ≤
      (C d + A d - hPos c.m c.D a S d + 2 ^ (c.w - 1)).toNat := by
    have hl : (enc c.w c.D fun d => C d + A d - hPos c.m c.D a S d) &&& c.RD =
        pack c.w c.D fun d => if 2 ^ (c.w - 1) ≤
          (C d + A d - hPos c.m c.D a S d + 2 ^ (c.w - 1)).toNat then 2 ^ (c.w - 1) else 0 := by
      rw [hRD, enc, rep, pack_land hZf fun _ _ => hOw]
      refine pack_congr fun d hd => ?_
      have hlt : (C d + A d - hPos c.m c.D a S d + 2 ^ (c.w - 1)).toNat < 2 ^ (c.w - 1 + 1) := by
        rw [Nat.sub_add_cancel hw]; exact hZf d hd
      exact land_two_pow hlt
    rw [hl, hRD, rep] at hguard
    intro d hd
    have := pack_inj (fun d _ => by split_ifs <;> omega) (fun _ _ => hOw) hguard d hd
    by_contra hne
    simp only [hne, ite_false] at this
    have : 0 < 2 ^ (c.w - 1) := by positivity
    omega
  have hfit : ∀ d < c.D, 0 ≤ C d + A d - hPos c.m c.D a S d := by
    intro d hd
    have h1 : ((2 ^ (c.w - 1) : ℕ) : ℤ) ≤
        ((C d + A d - hPos c.m c.D a S d + 2 ^ (c.w - 1)).toNat : ℤ) := by
      exact_mod_cast hdec d hd
    rw [Int.toNat_of_nonneg (by have := abs_lt.1 (hZ d hd); linarith)] at h1
    push_cast at h1; linarith
  refine ⟨hfit, ?_⟩
  have hmod : (enc c.w c.D fun d => C d + A d - hPos c.m c.D a S d) % 2 ^ c.w =
      (C 0 + A 0 - hPos c.m c.D a S 0 + 2 ^ (c.w - 1)).toNat := by
    rw [enc, pack_mod_of_pos hD (hZf 0 hD)]
  rw [hmod] at hlow
  have h1 : ((2 ^ (c.w - 1) : ℕ) : ℤ) <
      ((C 0 + A 0 - hPos c.m c.D a S 0 + 2 ^ (c.w - 1)).toNat : ℤ) := by exact_mod_cast hlow
  rw [Int.toNat_of_nonneg (by have := abs_lt.1 (hZ 0 hD); linarith)] at h1
  push_cast at h1; linarith

/-! ## Field sizes -/

/-- `∑ₑ f (eD+d)`: coefficient `d` summed over the entries. -/
def colSum (m D : ℕ) (f : ℕ → ℤ) (d : ℕ) : ℤ := ∑ e ∈ range m, f (e * D + d)

/-- One global size condition keeps every packed field inside its `w` bits: `Bf i` bounds
`|aᵢ|` plus the absolute contributions of the undecided cells at every node. -/
def SizeOK (c : Cfg) (Bf t : ℕ → ℤ) : Prop :=
  4 * c.m * ∑ i ∈ range (c.m * c.D), Bf i + ∑ d ∈ range c.D, |t d| < 2 ^ (c.w - 1)

theorem SizeOK.base {c : Cfg} {Bf t : ℕ → ℤ} (h : SizeOK c Bf t) (hm : 0 < c.m)
    (hB : 0 ≤ ∑ i ∈ range (c.m * c.D), Bf i) :
    4 * ∑ i ∈ range (c.m * c.D), Bf i + ∑ d ∈ range c.D, |t d| < 2 ^ (c.w - 1) := by
  unfold SizeOK at h
  have : (1 : ℤ) ≤ c.m := by exact_mod_cast hm
  nlinarith

theorem abs_colSum_le {m D d : ℕ} {f g : ℕ → ℤ} (h : ∀ e < m, |f (e * D + d)| ≤ g (e * D + d)) :
    |colSum m D f d| ≤ colSum m D g d :=
  (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun e he => h e (mem_range.1 he))

/-- The fields at a node whose accumulated table `a` and undecided cells `rem` satisfy the
size invariant all fit. -/
theorem fits_of_inv {c : Cfg} (hm : 0 < c.m) {T : ℕ → ℕ → ℤ} {t Bf : ℕ → ℤ}
    (hsize : SizeOK c Bf t) {a : ℕ → ℤ} {rem : List ℕ}
    (hinv : ∀ i < c.m * c.D, |a i| + absT T rem i ≤ Bf i) :
    Fits c.w (c.m * c.D) a ∧ Fits c.w (c.m * c.D) (sumT T rem) ∧
      Fits c.w (c.m * c.D) (fun i => 2 * a i + sumT T rem i) ∧
      Fits c.w c.D (colSum c.m c.D a) ∧
      Fits c.w c.D (fun d => t d + colSum c.m c.D (loT T rem) d) ∧
      Fits c.w c.D (fun d => t d + colSum c.m c.D (loT T rem) d + colSum c.m c.D a d) ∧
      Fits c.w c.D (fun d => t d + colSum c.m c.D (loT T rem) d + colSum c.m c.D a d -
        hPos c.m c.D a (sumT T rem) d) ∧
      ∃ F : ℕ, (∀ i < c.m * c.D, |2 * a i + sumT T rem i| ≤ F) ∧ c.m * F < 2 ^ c.w := by
  set N := c.m * c.D
  set B := ∑ i ∈ range N, Bf i
  have hBf0 : ∀ i < N, 0 ≤ Bf i := fun i hi =>
    (add_nonneg (abs_nonneg _) (absT_nonneg T rem i)).trans (hinv i hi)
  have hBfB : ∀ i < N, Bf i ≤ B := fun i hi =>
    single_le_sum (fun j hj => hBf0 j (mem_range.1 hj)) (mem_range.2 hi)
  have hB0 : 0 ≤ B := sum_nonneg fun i hi => hBf0 i (mem_range.1 hi)
  have hT0 : 0 ≤ ∑ d ∈ range c.D, |t d| := sum_nonneg fun _ _ => abs_nonneg _
  have htd : ∀ d < c.D, |t d| ≤ ∑ d ∈ range c.D, |t d| := fun d hd =>
    single_le_sum (f := fun d => |t d|) (fun _ _ => abs_nonneg _) (mem_range.2 hd)
  have hcol : ∀ d < c.D, colSum c.m c.D Bf d ≤ B := fun d hd => col_le_total hBf0 hd
  have hidx : ∀ e < c.m, ∀ d < c.D, e * c.D + d < N := fun e he d hd => by
    show e * c.D + d < c.m * c.D; nlinarith
  have ha : ∀ i < N, |a i| ≤ Bf i := fun i hi =>
    le_trans (le_add_of_nonneg_right (absT_nonneg T rem i)) (hinv i hi)
  have hS : ∀ i < N, |sumT T rem i| ≤ Bf i := fun i hi =>
    (abs_sumT_le T rem i).trans (le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hinv i hi))
  have hX : ∀ i < N, |2 * a i + sumT T rem i| ≤ 2 * Bf i := by
    intro i hi
    have h1 := hinv i hi
    have h2 := abs_sumT_le T rem i
    calc |2 * a i + sumT T rem i| ≤ |2 * a i| + |sumT T rem i| := abs_add_le _ _
      _ = 2 * |a i| + |sumT T rem i| := by rw [abs_mul]; norm_num
      _ ≤ 2 * Bf i := by linarith [abs_nonneg (a i), ha i hi]
  have hA : ∀ d < c.D, |colSum c.m c.D a d| ≤ B := fun d hd =>
    (abs_colSum_le fun e he => ha _ (hidx e he d hd)).trans (hcol d hd)
  have hlo : ∀ d < c.D, |colSum c.m c.D (loT T rem) d| ≤ B := fun d hd =>
    (abs_colSum_le fun e he => (abs_loT_le T rem _).trans
      (le_trans (le_add_of_nonneg_left (abs_nonneg _)) (hinv _ (hidx e he d hd)))).trans
      (hcol d hd)
  have hh : ∀ d < c.D, 0 ≤ hPos c.m c.D a (sumT T rem) d ∧
      hPos c.m c.D a (sumT T rem) d ≤ 2 * B := by
    intro d hd
    refine ⟨sum_nonneg fun _ _ => le_max_right _ _, ?_⟩
    calc hPos c.m c.D a (sumT T rem) d ≤ colSum c.m c.D (fun i => 2 * Bf i) d := by
          refine sum_le_sum fun e he => ?_
          have := abs_le.1 (hX _ (hidx e (mem_range.1 he) d hd))
          exact max_le (by linarith) (by linarith [hBf0 _ (hidx e (mem_range.1 he) d hd)])
      _ = 2 * colSum c.m c.D Bf d := by simp [colSum, mul_sum]
      _ ≤ 2 * B := by linarith [hcol d hd]
  have hO := hsize.base hm hB0
  have hmB : (c.m : ℤ) * (2 * B) < 2 ^ c.w := by
    have h := hsize; unfold SizeOK at h
    have h2 : (2 : ℤ) ^ (c.w - 1) ≤ 2 ^ c.w := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ 1)
    have h3 : (0 : ℤ) ≤ c.m * B := mul_nonneg (by positivity) hB0
    linarith
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun d hd => ?_, fun d hd => ?_,
    fun d hd => ?_, fun d hd => ?_, ⟨(2 * B).toNat, fun i hi => ?_, ?_⟩⟩
  · linarith [ha i hi, hBfB i hi]
  · linarith [hS i hi, hBfB i hi]
  · linarith [hX i hi, hBfB i hi]
  · linarith [hA d hd]
  · calc |t d + colSum c.m c.D (loT T rem) d| ≤ |t d| + |colSum c.m c.D (loT T rem) d| :=
          abs_add_le _ _
      _ < 2 ^ (c.w - 1) := by linarith [htd d hd, hlo d hd]
  · calc |t d + colSum c.m c.D (loT T rem) d + colSum c.m c.D a d|
        ≤ |t d| + |colSum c.m c.D (loT T rem) d| + |colSum c.m c.D a d| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ < 2 ^ (c.w - 1) := by linarith [htd d hd, hlo d hd, hA d hd]
  · obtain ⟨hh0, hh1⟩ := hh d hd
    calc |t d + colSum c.m c.D (loT T rem) d + colSum c.m c.D a d -
          hPos c.m c.D a (sumT T rem) d|
        ≤ |t d| + |colSum c.m c.D (loT T rem) d| + |colSum c.m c.D a d| +
            |hPos c.m c.D a (sumT T rem) d| :=
          (abs_sub _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)
      _ < 2 ^ (c.w - 1) := by
          rw [abs_of_nonneg hh0]; linarith [htd d hd, hlo d hd, hA d hd]
  · rw [Int.toNat_of_nonneg (by linarith)]; linarith [hX i hi, hBfB i hi]
  · have : ((c.m * (2 * B).toNat : ℕ) : ℤ) < 2 ^ c.w := by
      push_cast; rw [Int.toNat_of_nonneg (by linarith)]; exact hmB
    exact_mod_cast this

theorem fits_of_le {c : Cfg} (hm : 0 < c.m) {Bf t : ℕ → ℤ} (hsize : SizeOK c Bf t)
    (hBf0 : ∀ i < c.m * c.D, 0 ≤ Bf i) {f : ℕ → ℤ} (hf : ∀ i < c.m * c.D, |f i| ≤ Bf i) :
    Fits c.w (c.m * c.D) f := by
  intro i hi
  have hle : Bf i ≤ ∑ j ∈ range (c.m * c.D), Bf j :=
    single_le_sum (fun j hj => hBf0 j (mem_range.1 hj)) (mem_range.2 hi)
  have hB0 : 0 ≤ ∑ j ∈ range (c.m * c.D), Bf j := sum_nonneg fun j hj => hBf0 j (mem_range.1 hj)
  have := hsize.base hm hB0
  have hT0 : 0 ≤ ∑ d ∈ range c.D, |t d| := sum_nonneg fun _ _ => abs_nonneg _
  linarith [hf i hi]

theorem fits_colSum_of_le {c : Cfg} (hm : 0 < c.m) {Bf t : ℕ → ℤ} (hsize : SizeOK c Bf t)
    (hBf0 : ∀ i < c.m * c.D, 0 ≤ Bf i) {f : ℕ → ℤ} (hf : ∀ i < c.m * c.D, |f i| ≤ Bf i) :
    Fits c.w c.D (colSum c.m c.D f) := by
  intro d hd
  have hcol : |colSum c.m c.D f d| ≤ ∑ j ∈ range (c.m * c.D), Bf j := by
    refine (abs_colSum_le fun e he => hf _ ?_).trans (col_le_total hBf0 hd)
    nlinarith
  have hB0 : 0 ≤ ∑ j ∈ range (c.m * c.D), Bf j := sum_nonneg fun j hj => hBf0 j (mem_range.1 hj)
  have := hsize.base hm hB0
  have hT0 : 0 ≤ ∑ d ∈ range c.D, |t d| := sum_nonneg fun _ _ => abs_nonneg _
  linarith

/-! ## Bitmask paths -/

/-- The bitmask a search over the cells `ks` reaches when it follows the mask `L`. -/
def runMask (L : List Bool) : List ℕ → ℕ → ℕ
  | [], path => path
  | k :: ks, path => runMask L ks (if bit L k then path + 2 ^ k else path)

theorem runMask_eq (L : List Bool) (ks : List ℕ) (path : ℕ) :
    runMask L ks path = path + (ks.map fun k => if bit L k then 2 ^ k else 0).sum := by
  induction ks generalizing path with
  | nil => simp [runMask]
  | cons k ks ih =>
    simp only [runMask, ih, List.map_cons, List.sum_cons]
    split_ifs <;> ring

/-- The bitmask of `L` on cells `0, …, N-1`. -/
def maskOf (N : ℕ) (L : List Bool) : ℕ := pack 1 N fun k => if bit L k then 1 else 0

theorem sum_map_range (f : ℕ → ℕ) (N : ℕ) :
    ((List.range N).map f).sum = ∑ i ∈ range N, f i := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem runMask_perm {ks : List ℕ} {N : ℕ} (hperm : ks.Perm (List.range N)) (L : List Bool) :
    runMask L ks 0 = maskOf N L := by
  rw [runMask_eq, Nat.zero_add, (hperm.map _).sum_eq, sum_map_range, maskOf, pack]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

theorem maskOf_inj {N : ℕ} {L L' : List Bool} (hL : L.length = N) (hL' : L'.length = N)
    (h : maskOf N L = maskOf N L') : L = L' := by
  have hb := pack_inj (fun k _ => by split_ifs <;> simp) (fun k _ => by split_ifs <;> simp) h
  refine bit_ext (hL.trans hL'.symm) fun k hk => ?_
  have := hb k (hL ▸ hk)
  split_ifs at this with h₁ h₂ h₂ <;> simp_all

/-- `maskOf` by recursion, for the kernel. -/
def maskC : List Bool → ℕ
  | [] => 0
  | c :: L => (if c then 1 else 0) + 2 * maskC L

theorem maskC_eq (L : List Bool) : maskC L = maskOf L.length L := by
  induction L with
  | nil => simp [maskC, maskOf]
  | cons c L ih =>
    rw [maskC, ih, maskOf, maskOf, List.length_cons, pack_succ]
    simp only [bit_cons_zero, bit_cons_succ, pow_one]
    rfl

/-! ## The search -/

/-- One decision with its packed data: the cell, its table, its column sums, and for the
undecided cells from this one on, their sum `S` and `target + ∑ₑ lo`. -/
structure PStep where
  cell : ℕ
  tab : ℕ
  tsum : ℕ
  s : ℕ
  c : ℕ

/-- The packed data of the steps over the undecided cells `rem`. -/
def StepsOK (c : Cfg) (T : ℕ → ℕ → ℤ) (t : ℕ → ℤ) : List PStep → List ℕ → Prop
  | [], [] => True
  | st :: ss, k :: rem =>
    st.cell = k ∧ st.tab = enc c.w (c.m * c.D) (T k) ∧
      st.tsum = enc c.w c.D (colSum c.m c.D (T k)) ∧
      st.s = enc c.w (c.m * c.D) (sumT T (k :: rem)) ∧
      st.c = enc c.w c.D (fun d => t d + colSum c.m c.D (loT T (k :: rem)) d) ∧
      StepsOK c T t ss rem
  | _, _ => False

/-- Branch and bound over packed states `acc = enc a`, `accSum = enc (colSum a)`; the path is
the bitmask of the selected cells. -/
def bnbP (c : Cfg) (allowed : List ℕ) (leafS leafC : ℕ) :
    List PStep → ℕ → ℕ → ℕ → Bool
  | [], path, acc, accSum => nodeTest c leafS leafC acc accSum || allowed.contains path
  | st :: ss, path, acc, accSum =>
    nodeTest c st.s st.c acc accSum ||
      (bnbP c allowed leafS leafC ss path acc accSum &&
        bnbP c allowed leafS leafC ss (path + 2 ^ st.cell) (acc + st.tab - c.RN)
          (accSum + st.tsum - c.RD))

/-- A passing node test bounds the energy of every completion below the target. -/
theorem energy_lt_of_nodeTest {c : Cfg} (hc : c.OK) {T : ℕ → ℕ → ℤ} {t Bf : ℕ → ℤ}
    (hsize : SizeOK c Bf t) {a : ℕ → ℤ} {rem : List ℕ}
    (hinv : ∀ i < c.m * c.D, |a i| + absT T rem i ≤ Bf i)
    (h : nodeTest c (enc c.w (c.m * c.D) (sumT T rem))
      (enc c.w c.D (fun d => t d + colSum c.m c.D (loT T rem) d))
      (enc c.w (c.m * c.D) a) (enc c.w c.D (colSum c.m c.D a)) = true)
    (L : List Bool) {ω : ℕ → ℤ} (hω : Weights ω) :
    energy c.m c.D (fun i => a i + chosenT T L rem i) ω < ∑ d ∈ range c.D, t d * ω d := by
  obtain ⟨ha, hS, hX, hA, hC, hCA, hZ, F, hXF, hmF⟩ := fits_of_inv hc.hm hsize hinv
  obtain ⟨hz, hz0⟩ := nodeTest_spec hc ha hS hX hC hA hCA hZ hXF hmF h
  refine (energy_le c.m c.D T L rem a hω).trans_lt ?_
  rw [← sub_pos, ← sum_sub_distrib]
  simp only [← sub_mul]
  have key : ∀ d, t d - beta c.m c.D a (sumT T rem) (loT T rem) d =
      t d + colSum c.m c.D (loT T rem) d + colSum c.m c.D a d - hPos c.m c.D a (sumT T rem) d := by
    intro d
    simp only [beta, colSum, hPos, sum_add_distrib, sum_sub_distrib, sum_neg_distrib]
    ring
  simp only [key]
  exact sum_pos_of_coeffs hc.hD hz0 hz hω

theorem bnbP_sound {c : Cfg} (hc : c.OK) {T : ℕ → ℕ → ℤ} {t Bf : ℕ → ℤ}
    (hsize : SizeOK c Bf t) {allowed : List ℕ} {leafS leafC : ℕ}
    (hleafS : leafS = enc c.w (c.m * c.D) (sumT T [])) (hleafC : leafC = enc c.w c.D t) :
    ∀ (rem : List ℕ) (ss : List PStep), StepsOK c T t ss rem →
    ∀ (path : ℕ) (a : ℕ → ℤ), (∀ i < c.m * c.D, |a i| + absT T rem i ≤ Bf i) →
    bnbP c allowed leafS leafC ss path (enc c.w (c.m * c.D) a)
      (enc c.w c.D (colSum c.m c.D a)) = true →
    ∀ (L : List Bool) {ω : ℕ → ℤ}, Weights ω →
      runMask L rem path ∈ allowed ∨
        energy c.m c.D (fun i => a i + chosenT T L rem i) ω < ∑ d ∈ range c.D, t d * ω d := by
  intro rem
  induction rem with
  | nil =>
    intro ss hss path a hinv h L ω hω
    cases ss with
    | cons _ _ => exact absurd hss (by simp [StepsOK])
    | nil =>
      simp only [bnbP, Bool.or_eq_true, List.contains_iff_mem] at h
      rcases h with h | h
      · refine Or.inr (energy_lt_of_nodeTest hc hsize hinv ?_ L hω)
        have hlc : leafC = enc c.w c.D (fun d => t d + colSum c.m c.D (loT T []) d) := by
          rw [hleafC]; simp [colSum]
        rwa [hleafS, hlc] at h
      · exact Or.inl h
  | cons k rem ih =>
    intro ss hss path a hinv h L ω hω
    cases ss with
    | nil => exact absurd hss (by simp [StepsOK])
    | cons st ss =>
      obtain ⟨hcell, htab, htsum, hs, hcc, hss'⟩ := hss
      simp only [bnbP, Bool.or_eq_true, Bool.and_eq_true] at h
      rcases h with h | ⟨h₀, h₁⟩
      · rw [hs, hcc] at h
        exact Or.inr (energy_lt_of_nodeTest hc hsize hinv h L hω)
      · have hinv' : ∀ i < c.m * c.D, |a i| + absT T rem i ≤ Bf i := fun i hi => by
          have := hinv i hi; rw [absT_cons] at this; linarith [abs_nonneg (T k i)]
        cases hb : bit L k
        · have := ih ss hss' path a hinv' h₀ L hω
          simpa [runMask, chosenT_cons, hb] using this
        · -- the packed state after selecting `k`
          have hinv'' : ∀ i < c.m * c.D, |a i + T k i| + absT T rem i ≤ Bf i := fun i hi => by
            have := hinv i hi; rw [absT_cons] at this
            linarith [abs_add_le (a i) (T k i)]
          obtain ⟨ha', -, -, hA', -, -, -, -⟩ := fits_of_inv hc.hm hsize hinv''
          obtain ⟨ha, -, -, hA, -, -, -, -⟩ := fits_of_inv hc.hm hsize hinv
          have hTkle : ∀ i < c.m * c.D, |T k i| ≤ Bf i := fun i hi => by
            have := hinv i hi; rw [absT_cons] at this
            linarith [abs_nonneg (a i), absT_nonneg T rem i]
          have hBf0 : ∀ i < c.m * c.D, 0 ≤ Bf i := fun i hi =>
            (add_nonneg (abs_nonneg _) (absT_nonneg T _ i)).trans (hinv i hi)
          have hTk := fits_of_le hc.hm hsize hBf0 hTkle
          have hTkc := fits_colSum_of_le hc.hm hsize hBf0 hTkle
          have hacc : enc c.w (c.m * c.D) a + enc c.w (c.m * c.D) (T k) - c.RN =
              enc c.w (c.m * c.D) (fun i => a i + T k i) := by
            refine sub_eq_enc ha' ?_
            rw [hc.hRN]; push_cast
            rw [cast_enc ha, cast_enc hTk, cast_rep, packZ_add]
            push_cast; ring
          have hcol : colSum c.m c.D (fun i => a i + T k i) =
              fun d => colSum c.m c.D a d + colSum c.m c.D (T k) d := by
            funext d; simp [colSum, sum_add_distrib]
          have haccS : enc c.w c.D (colSum c.m c.D a) + enc c.w c.D (colSum c.m c.D (T k)) - c.RD =
              enc c.w c.D (colSum c.m c.D (fun i => a i + T k i)) := by
            refine sub_eq_enc hA' ?_
            rw [hc.hRD, hcol]; push_cast
            rw [cast_enc hA, cast_enc hTkc, cast_rep, packZ_add]
            push_cast; ring
          rw [hcell, htab, htsum, hacc, haccS] at h₁
          have := ih ss hss' (path + 2 ^ k) (fun i => a i + T k i) hinv'' h₁ L hω
          simpa [runMask, chosenT_cons, hb, add_assoc] using this

end Solved.Cert.Packed
