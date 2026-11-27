import Research.ICGGeneralBridge

/-!
# The spectral bridge for orders with any number of distinct primes

For distinct primes `r 0, …, r (k-1)` and exponents `a`, the energy of the integral circulant
graph `ICG(∏ᵢ rᵢ^{aᵢ}, D)` equals `∑ᵤ |∑_c [∏ᵢ rᵢ^{cᵢ} ∈ D] ∏ᵢ Tent rᵢ aᵢ uᵢ cᵢ|`, both sums over
the exponent box `∏ᵢ [0, aᵢ]` (`energy_icgAdj_multi`). For `k = 2` this is H. Dong's
`ICGGeneral.energy_icgAdj_pq` (ai4math-results, Apache-2.0), whose general parts are reused:
the circulant spectrum is the DFT of the connection function
(`ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft`), and sums of additive characters over the
multiples of `m` (`ICGBridge.sum_dvd_stdAddChar`). The two-prime steps are replaced by their
`k`-fold versions: unique exponent vectors of divisors, inclusion–exclusion over subsets of the
primes (`Finset.prod_sub`), and multiplicativity of Euler's totient.
-/

noncomputable section

namespace Solved.ICG.Multi

open Finset ZMod ICGGeneral

variable {k : ℕ}

/-- `∏ᵢ rᵢ^{xᵢ}`. -/
def pw (r x : Fin k → ℕ) : ℕ := ∏ i, r i ^ x i

/-- The exponent box `∏ᵢ [0, aᵢ]`. -/
def box (a : Fin k → ℕ) : Finset (Fin k → ℕ) := Fintype.piFinset fun i => range (a i + 1)

/-- Pairwise distinct primes. -/
structure Primes (r : Fin k → ℕ) : Prop where
  prime : ∀ i, (r i).Prime
  inj : Function.Injective r

variable {r : Fin k → ℕ}

theorem mem_box {a x : Fin k → ℕ} : x ∈ box a ↔ ∀ i, x i ≤ a i := by
  simp [box]

/-! ## Exponent vectors of divisors -/

theorem pw_ne_zero (hr : Primes r) (x : Fin k → ℕ) : pw r x ≠ 0 :=
  prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hr.prime i).ne_zero

theorem pw_add (r x y : Fin k → ℕ) : pw r (x + y) = pw r x * pw r y := by
  simp only [pw, Pi.add_apply, pow_add, prod_mul_distrib]

theorem factorization_pw (hr : Primes r) (x : Fin k → ℕ) (p : ℕ) :
    (pw r x).factorization p = ∑ j, if r j = p then x j else 0 := by
  rw [pw, Nat.factorization_prod fun i _ => pow_ne_zero _ (hr.prime i).ne_zero,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [(hr.prime j).factorization_pow, Finsupp.single_apply]

theorem factorization_pw_self (hr : Primes r) (x : Fin k → ℕ) (i : Fin k) :
    (pw r x).factorization (r i) = x i := by
  rw [factorization_pw hr]
  simp only [hr.inj.eq_iff]
  simp

theorem pw_dvd_pw_iff (hr : Primes r) {x c : Fin k → ℕ} : pw r x ∣ pw r c ↔ ∀ i, x i ≤ c i := by
  constructor
  · intro h i
    have := (Nat.factorization_le_iff_dvd (pw_ne_zero hr x) (pw_ne_zero hr c)).2 h (r i)
    rwa [factorization_pw_self hr, factorization_pw_self hr] at this
  · intro h
    exact prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow _ (h i)

theorem pw_inj (hr : Primes r) {x c : Fin k → ℕ} : pw r x = pw r c ↔ x = c := by
  constructor
  · intro h
    funext i
    rw [← factorization_pw_self hr x i, h, factorization_pw_self hr]
  · rintro rfl; rfl

/-- Every divisor of `∏ rᵢ^{aᵢ}` is `∏ rᵢ^{cᵢ}` with `c ≤ a`. -/
theorem dvd_rep (hr : Primes r) {a : Fin k → ℕ} {d : ℕ} (hd : d ∣ pw r a) :
    ∃ c ∈ box a, d = pw r c := by
  have hd0 : d ≠ 0 := fun h => pw_ne_zero hr a (zero_dvd_iff.1 (h ▸ hd))
  have hle := (Nat.factorization_le_iff_dvd hd0 (pw_ne_zero hr a)).2 hd
  refine ⟨fun i => d.factorization (r i), mem_box.2 fun i => ?_, ?_⟩
  · have := hle (r i); rwa [factorization_pw_self hr] at this
  · refine Nat.eq_of_factorization_eq hd0 (pw_ne_zero hr _) fun p => ?_
    rw [factorization_pw hr]
    by_cases hp : ∃ i, r i = p
    · obtain ⟨i, rfl⟩ := hp
      simp only [hr.inj.eq_iff]
      simp
    · push Not at hp
      have h0 : (pw r a).factorization p = 0 := by
        rw [factorization_pw hr]; exact sum_eq_zero fun j _ => ite_eq_right (hp j)
      have := hle p
      rw [h0] at this
      rw [Nat.le_zero.1 this]
      exact (sum_eq_zero fun j _ => ite_eq_right (hp j)).symm

theorem coprime_pow (hr : Primes r) {i j : Fin k} (hij : i ≠ j) (m n : ℕ) :
    Nat.Coprime (r i ^ m) (r j ^ n) :=
  Nat.Coprime.pow _ _ ((Nat.coprime_primes (hr.prime i) (hr.prime j)).2 (hr.inj.ne hij))

theorem prod_dvd_of_forall (hr : Primes r) (x : Fin k → ℕ) {v : ℕ} (s : Finset (Fin k))
    (h : ∀ i ∈ s, r i ^ x i ∣ v) : ∏ i ∈ s, r i ^ x i ∣ v := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj]
    refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ (h j (mem_insert_self j s))
      (ih fun i hi => h i (mem_insert_of_mem hi))
    exact Nat.Coprime.prod_right fun i hi => coprime_pow hr (by rintro rfl; exact hj hi) _ _

theorem pw_dvd_iff (hr : Primes r) (x : Fin k → ℕ) (v : ℕ) :
    pw r x ∣ v ↔ ∀ i, r i ^ x i ∣ v :=
  ⟨fun h i => (dvd_prod_of_mem _ (mem_univ i)).trans h,
    fun h => prod_dvd_of_forall hr x univ fun i _ => h i⟩

/-- With `gcd(v, N) = ∏ rᵢ^{gᵢ}` and `x ≤ a`, `∏ rᵢ^{xᵢ} ∣ v` iff `x ≤ g`. -/
theorem dvd_iff_of_gcd (hr : Primes r) {a : Fin k → ℕ} {v : ℕ} {g x : Fin k → ℕ}
    (hg : Nat.gcd v (pw r a) = pw r g) (hx : ∀ i, x i ≤ a i) :
    pw r x ∣ v ↔ ∀ i, x i ≤ g i := by
  rw [← pw_dvd_pw_iff hr, ← hg, Nat.dvd_gcd_iff]
  exact ⟨fun h => ⟨h, (pw_dvd_pw_iff hr).2 hx⟩, fun h => h.1⟩

/-! ## The DFT of divisibility indicators -/

/-- `[x ≤ a ∧ ∏ rᵢ^{xᵢ} ∣ v]`. -/
def ind (r a : Fin k → ℕ) (v : ℕ) (x : Fin k → ℕ) : ℤ :=
  if (∀ i, x i ≤ a i) ∧ pw r x ∣ v then 1 else 0

theorem prod_ite_zero' {M : Type*} [CommMonoidWithZero M] (P : Fin k → Prop) [DecidablePred P]
    (f : Fin k → M) : (∏ i, if P i then f i else 0) = if ∀ i, P i then ∏ i, f i else 0 := by
  rw [Finset.prod_ite_zero]
  simp

theorem dft_ind (hr : Primes r) {a : Fin k → ℕ} [NeZero (pw r a)] (κ : ZMod (pw r a))
    {u : Fin k → ℕ} (hκ : Nat.gcd κ.val (pw r a) = pw r u) (x : Fin k → ℕ) :
    ∑ s : ZMod (pw r a), stdAddChar (-(s * κ)) * ((ind r a s.val x : ℤ) : ℂ) =
      ((∏ i, Spow (r i) (a i) (x i) (u i) : ℤ) : ℂ) := by
  by_cases hx : ∀ i, x i ≤ a i
  · have hmL : pw r x * pw r (a - x) = pw r a := by
      rw [← pw_add]; congr 1; funext i; simp [Nat.add_sub_cancel' (hx i)]
    have h1 := ICGBridge.sum_dvd_stdAddChar (pw r x) (pw r (a - x)) hmL κ
    have h2 : ∀ s : ZMod (pw r a), stdAddChar (-(s * κ)) * ((ind r a s.val x : ℤ) : ℂ) =
        if pw r x ∣ s.val then stdAddChar (-(s * κ)) else 0 := by
      intro s
      unfold ind
      by_cases hd : pw r x ∣ s.val <;> simp [hd, hx]
    rw [sum_congr rfl fun s _ => h2 s, h1]
    have hiff := dvd_iff_of_gcd hr (x := a - x) hκ fun i => Nat.sub_le _ _
    unfold Spow
    rw [prod_ite_zero']
    by_cases hc : ∀ i, a i - x i ≤ u i
    · rw [ite_eq_left (hiff.2 hc), ite_eq_left fun i => ⟨hx i, hc i⟩]
      push_cast [pw]
      rfl
    · rw [ite_eq_right fun h => hc (hiff.1 h), ite_eq_right fun h => hc fun i => (h i).2]
      simp
  · have h0 : ∀ s : ZMod (pw r a), ind r a s.val x = 0 := fun s => by
      unfold ind; rw [ite_eq_right fun h => hx h.1]
    simp only [h0, Int.cast_zero, mul_zero, sum_const_zero]
    push Not at hx
    obtain ⟨i, hi⟩ := hx
    rw [prod_eq_zero (mem_univ i)]
    · simp
    · unfold Spow; rw [ite_eq_right fun h => absurd h.1 (not_le.2 hi)]

/-! ## Inclusion–exclusion over subsets of the primes -/

/-- `c + 1_t`. -/
def bump (c : Fin k → ℕ) (t : Finset (Fin k)) : Fin k → ℕ := fun i => if i ∈ t then c i + 1 else c i

theorem prod_ite_mem {M : Type*} [CommMonoid M] (t : Finset (Fin k)) (A B : Fin k → M) :
    (∏ i, if i ∈ t then B i else A i) = (∏ i ∈ univ \ t, A i) * ∏ i ∈ t, B i := by
  rw [prod_ite, mul_comm]
  congr 1
  · congr 1; ext i; simp
  · congr 1; ext i; simp

/-- `∏ᵢ (Aᵢ - Bᵢ) = ∑ₜ (-1)^{|t|} ∏ᵢ (Bᵢ if i ∈ t else Aᵢ)`. -/
theorem prod_sub_ite {R : Type*} [CommRing R] (A B : Fin k → R) :
    ∏ i, (A i - B i) = ∑ t ∈ (univ : Finset (Fin k)).powerset,
      (-1) ^ t.card * ∏ i, (if i ∈ t then B i else A i) := by
  rw [prod_sub]
  refine sum_congr rfl fun t _ => ?_
  rw [prod_ite_mem, mul_assoc]

/-- The gcd-class indicator by inclusion–exclusion. -/
theorem gcd_class (hr : Primes r) {a : Fin k → ℕ} (v : ℕ) {c : Fin k → ℕ} (hc : ∀ i, c i ≤ a i) :
    (if Nat.gcd v (pw r a) = pw r c then (1 : ℤ) else 0) =
      ∑ t ∈ (univ : Finset (Fin k)).powerset, (-1) ^ t.card * ind r a v (bump c t) := by
  obtain ⟨g, hgbox, hg⟩ := dvd_rep hr (Nat.gcd_dvd_right v (pw r a))
  have hga := mem_box.1 hgbox
  have hind : ∀ t, ind r a v (bump c t) = if ∀ i, bump c t i ≤ g i then 1 else 0 := by
    intro t
    unfold ind
    by_cases hb : ∀ i, bump c t i ≤ g i
    · rw [ite_eq_left hb, ite_eq_left ⟨fun i => (hb i).trans (hga i),
        (dvd_iff_of_gcd hr hg fun i => (hb i).trans (hga i)).2 hb⟩]
    · rw [ite_eq_right hb, ite_eq_right fun h => hb ((dvd_iff_of_gcd hr hg h.1).1 h.2)]
  have hprod : ∀ t : Finset (Fin k), (if ∀ i, bump c t i ≤ g i then (1 : ℤ) else 0) =
      ∏ i, (if i ∈ t then (if c i + 1 ≤ g i then (1 : ℤ) else 0)
        else (if c i ≤ g i then 1 else 0)) := by
    intro t
    have : ∀ i, (if i ∈ t then (if c i + 1 ≤ g i then (1 : ℤ) else 0)
        else (if c i ≤ g i then 1 else 0)) = if bump c t i ≤ g i then 1 else 0 := by
      intro i; unfold bump; by_cases hi : i ∈ t <;> simp [hi]
    rw [prod_congr rfl fun i _ => this i, prod_boole]
    simp
  have key : ∑ t ∈ (univ : Finset (Fin k)).powerset, (-1) ^ t.card * ind r a v (bump c t) =
      ∏ i, ((if c i ≤ g i then (1 : ℤ) else 0) - if c i + 1 ≤ g i then 1 else 0) := by
    rw [prod_sub_ite]
    exact sum_congr rfl fun t _ => by rw [hind, hprod]
  have hdiff : ∀ i, ((if c i ≤ g i then (1 : ℤ) else 0) - if c i + 1 ≤ g i then 1 else 0) =
      if g i = c i then 1 else 0 := by
    intro i; split_ifs <;> omega
  rw [key, prod_congr rfl fun i _ => hdiff i, prod_boole, hg]
  simp only [pw_inj hr]
  by_cases h : g = c
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right fun h' => h (funext fun i => h' i (mem_univ i))]

/-- The DFT of a gcd-class indicator: a product of prime-power Ramanujan sums. -/
theorem dft_gcd_class (hr : Primes r) {a : Fin k → ℕ} [NeZero (pw r a)] (κ : ZMod (pw r a))
    {u : Fin k → ℕ} (hκ : Nat.gcd κ.val (pw r a) = pw r u) {c : Fin k → ℕ} (hc : ∀ i, c i ≤ a i) :
    ∑ s : ZMod (pw r a), stdAddChar (-(s * κ)) *
        (if Nat.gcd s.val (pw r a) = pw r c then (1 : ℂ) else 0) =
      ((∏ i, (Spow (r i) (a i) (c i) (u i) - Spow (r i) (a i) (c i + 1) (u i)) : ℤ) : ℂ) := by
  have h1 : ∀ s : ZMod (pw r a), (if Nat.gcd s.val (pw r a) = pw r c then (1 : ℂ) else 0) =
      ∑ t ∈ (univ : Finset (Fin k)).powerset, (-1) ^ t.card * ((ind r a s.val (bump c t) : ℤ) : ℂ) := by
    intro s
    have h := congrArg (fun z : ℤ => (z : ℂ)) (gcd_class hr s.val hc)
    push_cast at h
    exact h
  simp_rw [h1, mul_sum, ← mul_assoc, mul_comm (stdAddChar _) ((-1 : ℂ) ^ _), mul_assoc]
  rw [sum_comm]
  simp_rw [← mul_sum, dft_ind hr κ hκ]
  rw [prod_sub_ite]
  push_cast
  refine sum_congr rfl fun t _ => ?_
  congr 1
  refine prod_congr rfl fun i _ => ?_
  unfold bump
  split_ifs <;> rfl

/-! ## The connection function -/

theorem conn_decomp (hr : Primes r) {a : Fin k → ℕ} (D : Finset ℕ) (w : ℕ) :
    (if Nat.gcd w (pw r a) ∈ D then (1 : ℂ) else 0) =
      ∑ c ∈ box a, if pw r c ∈ D then (if Nat.gcd w (pw r a) = pw r c then (1 : ℂ) else 0)
        else 0 := by
  obtain ⟨g, hgbox, hg⟩ := dvd_rep hr (Nat.gcd_dvd_right w (pw r a))
  rw [hg, sum_eq_single_of_mem g hgbox]
  · by_cases hD : pw r g ∈ D <;> simp [hD]
  · intro c _ hcg
    simp only [pw_inj hr]
    simp [Ne.symm hcg]

/-- The eigenvalue of the gcd class `u`. -/
def Lam (r a : Fin k → ℕ) (D : Finset ℕ) (u : Fin k → ℕ) : ℤ :=
  ∑ c ∈ box a, if pw r c ∈ D then
    ∏ i, (Spow (r i) (a i) (c i) (u i) - Spow (r i) (a i) (c i + 1) (u i)) else 0

theorem dft_connFun (hr : Primes r) {a : Fin k → ℕ} [NeZero (pw r a)] (D : Finset ℕ)
    (κ : ZMod (pw r a)) {u : Fin k → ℕ} (hκ : Nat.gcd κ.val (pw r a) = pw r u) :
    𝓕 (fun s : ZMod (pw r a) => ((ICGBridge.connFun (pw r a) D s : ℝ) : ℂ)) κ =
      ((Lam r a D u : ℤ) : ℂ) := by
  rw [dft_apply]
  have h1 : ∀ s : ZMod (pw r a), ((ICGBridge.connFun (pw r a) D s : ℝ) : ℂ) =
      ∑ c ∈ box a, if pw r c ∈ D then
        (if Nat.gcd s.val (pw r a) = pw r c then (1 : ℂ) else 0) else 0 := by
    intro s
    rw [← conn_decomp hr D s.val]
    unfold ICGBridge.connFun
    split_ifs <;> simp
  simp_rw [h1, smul_eq_mul, mul_sum]
  rw [sum_comm]
  unfold Lam
  push_cast
  refine sum_congr rfl fun c hc => ?_
  by_cases hD : pw r c ∈ D
  · simp only [hD, ite_true]
    have := dft_gcd_class hr κ hκ (mem_box.1 hc)
    push_cast at this
    exact this
  · simp [hD]

/-! ## Class sizes -/

theorem totient_prod (hr : Primes r) (x : Fin k → ℕ) (s : Finset (Fin k)) :
    Nat.totient (∏ i ∈ s, r i ^ x i) = ∏ i ∈ s, Nat.totient (r i ^ x i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, Nat.totient_mul, ih]
    exact Nat.Coprime.prod_right fun i hi => coprime_pow hr (by rintro rfl; exact hj hi) _ _

theorem totient_class (hr : Primes r) {a u : Fin k → ℕ} (hu : ∀ i, u i ≤ a i) :
    ((Nat.totient (pw r a / pw r u) : ℕ) : ℝ) = ∏ i, phiX (r i) (a i - u i) := by
  have hdiv : pw r a / pw r u = pw r (a - u) := by
    have : pw r a = pw r u * pw r (a - u) := by
      rw [← pw_add]; congr 1; funext i; simp [Nat.add_sub_cancel' (hu i)]
    rw [this, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (pw_ne_zero hr u))]
  rw [hdiv, pw, totient_prod hr]
  push_cast
  exact prod_congr rfl fun i _ => by rw [Pi.sub_apply, totient_prime_pow_cast (hr.prime i)]

theorem sum_norm_dft_connFun (hr : Primes r) {a : Fin k → ℕ} [NeZero (pw r a)] (D : Finset ℕ) :
    ∑ κ : ZMod (pw r a), ‖𝓕 (fun s : ZMod (pw r a) => ((ICGBridge.connFun (pw r a) D s : ℝ) : ℂ)) κ‖ =
      ∑ u ∈ box a, (Nat.totient (pw r a / pw r u) : ℝ) * |((Lam r a D u : ℤ) : ℝ)| := by
  set Λ : (Fin k → ℕ) → ℝ := fun u => |((Lam r a D u : ℤ) : ℝ)|
  set Φ : ℕ → ℝ := fun d => ∑ u ∈ box a, if d = pw r u then Λ u else 0
  have hκ : ∀ κ : ZMod (pw r a),
      ‖𝓕 (fun s : ZMod (pw r a) => ((ICGBridge.connFun (pw r a) D s : ℝ) : ℂ)) κ‖ =
        Φ (Nat.gcd κ.val (pw r a)) := by
    intro κ
    obtain ⟨g, hgbox, hg⟩ := dvd_rep hr (Nat.gcd_dvd_right κ.val (pw r a))
    rw [dft_connFun hr D κ hg, Complex.norm_intCast, hg]
    simp only [Φ, pw_inj hr]
    rw [sum_ite_eq _ _ _, ite_eq_left hgbox]
  rw [sum_congr rfl fun κ _ => hκ κ, ICGBridge.sum_zmod_val (N := pw r a)
    (fun w => Φ (Nat.gcd w (pw r a)))]
  simp only [Φ]
  rw [sum_comm]
  refine sum_congr rfl fun u hu => ?_
  have hsplit : ∀ w : ℕ, (if Nat.gcd w (pw r a) = pw r u then Λ u else 0) =
      (if (pw r a).gcd w = pw r u then (1 : ℝ) else 0) * Λ u := by
    intro w; rw [Nat.gcd_comm]; split_ifs <;> simp
  rw [sum_congr rfl fun w _ => hsplit w, ← sum_mul, sum_boole,
    ← Nat.totient_div_of_dvd ((pw_dvd_pw_iff hr).2 (mem_box.1 hu))]

/-! ## The bridge -/

theorem class_term (hr : Primes r) {a u : Fin k → ℕ} (hu : ∀ i, u i ≤ a i) (D : Finset ℕ) :
    ((Nat.totient (pw r a / pw r u) : ℕ) : ℝ) * |((Lam r a D u : ℤ) : ℝ)| =
      |∑ c ∈ box a, if pw r c ∈ D then ∏ i, Tent (r i) (a i) (u i) (c i) else 0| := by
  rw [totient_class hr hu]
  have hφ : 0 ≤ ∏ i, phiX (r i : ℝ) (a i - u i) :=
    prod_nonneg fun i _ => phiX_nonneg (by exact_mod_cast (hr.prime i).one_le) _
  rw [← abs_of_nonneg hφ, ← abs_mul]
  congr 1
  unfold Lam
  push_cast
  rw [mul_sum]
  refine sum_congr rfl fun c hc => ?_
  split_ifs
  · rw [← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    unfold Tent
    rw [ramX_eq_Spow (r i) ((mem_box.1 hc) i) (u i)]
  · simp

/-- **Spectral bridge for `k` distinct primes.** -/
theorem energy_icgAdj_multi (hr : Primes r) (a : Fin k → ℕ) (D : Finset ℕ) :
    ICGBridge.energy (ICGBridge.icgAdj (pw r a) D) (ICGBridge.icgAdj_isHermitian _ _) =
      ∑ u ∈ box a, |∑ c ∈ box a, if pw r c ∈ D then ∏ i, Tent (r i) (a i) (u i) (c i) else 0| := by
  have : NeZero (pw r a) := ⟨pw_ne_zero hr a⟩
  unfold ICGBridge.energy
  rw [ICGBridge.sum_abs_eigenvalues_eq_sum_norm_dft (ICGBridge.icgAdj (pw r a) D) _
      (ZMod.finEquiv (pw r a)).toEquiv (ICGBridge.connFun (pw r a) D)
      (ICGBridge.icgAdj_eq_connFun (pw r a) D),
    sum_norm_dft_connFun hr D]
  exact sum_congr rfl fun u hu => class_term hr (mem_box.1 hu) D

end Solved.ICG.Multi
