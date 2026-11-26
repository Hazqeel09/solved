import EffectiveCutoffs
import ControlInflation

namespace SolvedProfiles

def product : Nat → (Nat → Nat) → Nat
  | 0, _ => 1
  | n+1, f => product n f * f n

theorem product_congr (n : Nat) {f g : Nat → Nat}
    (same : ∀ i, i < n → f i = g i) : product n f = product n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [product, ih (fun i hi => same i (by omega)), same n (by omega)]

theorem product_mono (n : Nat) {f g : Nat → Nat}
    (bound : ∀ i, i < n → f i ≤ g i) : product n f ≤ product n g := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    exact Nat.mul_le_mul (ih (fun i hi => bound i (by omega))) (bound n (by omega))

theorem product_one (n : Nat) : product n (fun _ => 1) = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [product, ih, Nat.mul_one]

theorem product_positive (n : Nat) {f : Nat → Nat}
    (positive : ∀ i, 0 < f i) : 0 < product n f := by
  induction n with
  | zero => exact Nat.zero_lt_one
  | succ n ih => exact Nat.mul_pos ih (positive n)

theorem product_mul (n : Nat) (f g : Nat → Nat) :
    product n (fun i => f i*g i) = product n f * product n g := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [product, ih]; ac_rfl

theorem product_power (n q : Nat) (f : Nat → Nat) :
    product n (fun i => f i^q) = (product n f)^q := by
  induction n with
  | zero => simp only [product, Nat.one_pow]
  | succ n ih => simp only [product, ih, Nat.mul_pow]

theorem product_head (n : Nat) (f : Nat → Nat) :
    product (n+1) f = f 0 * product n (fun i => f (i+1)) := by
  induction n with
  | zero => simp only [product, Nat.one_mul, Nat.mul_one]
  | succ n ih => simp only [product] at *; rw [ih]; ac_rfl

structure Profile where
  coefficient : Nat → Nat
  constant : Bool

def monomial (k : Nat) (p : Profile) (x : Nat) :=
  product (k+1) (fun i => p.coefficient i ^ (x^i))

def fixed (b : Nat) : Profile :=
  ⟨(fun | 0 => b | _+1 => 1), true⟩

def multiply (p q : Profile) : Profile :=
  ⟨(fun i => p.coefficient i*q.coefficient i), p.constant && q.constant⟩

def power (p : Profile) (e : Nat) : Profile :=
  ⟨(fun i => p.coefficient i^e), p.constant⟩

def shift (p : Profile) : Profile :=
  ⟨(fun | 0 => 1 | i+1 => p.coefficient i), p.constant && (p.coefficient 0 == 1)⟩

def maximum (p q : Profile) : Profile :=
  ⟨(fun i => max (p.coefficient i) (q.coefficient i)), false⟩

def doubleConstant (p : Profile) : Profile :=
  ⟨(fun | 0 => 2*p.coefficient 0 | i+1 => p.coefficient (i+1)), false⟩

def add (p q : Profile) : Profile :=
  if p.constant && q.constant then fixed (p.coefficient 0+q.coefficient 0)
  else doubleConstant (maximum p q)

theorem monomial_fixed (k b x : Nat) : monomial k (fixed b) x = b := by
  rw [monomial, product_head]
  simp only [fixed, Nat.pow_zero, Nat.pow_one, Nat.one_pow, product_one, Nat.mul_one]

theorem monomial_multiply (k x : Nat) (p q : Profile) :
    monomial k (multiply p q) x = monomial k p x * monomial k q x := by
  simp only [monomial, multiply, Nat.mul_pow, product_mul]

theorem monomial_power (k x e : Nat) (p : Profile) :
    monomial k (power p e) x = (monomial k p x)^e := by
  simp only [monomial, power, Nat.pow_right_comm _ e, product_power]

theorem monomial_shift (k x : Nat) (p : Profile) :
    monomial (k+1) (shift p) x = (monomial k p x)^x := by
  rw [monomial, product_head]
  simp only [shift, Nat.pow_zero, Nat.pow_one, Nat.one_mul, Nat.pow_succ, Nat.pow_mul]
  exact product_power (k+1) x _

theorem monomial_double (k x : Nat) (p : Profile) :
    monomial k (doubleConstant p) x = 2*monomial k p x := by
  simp only [monomial, product_head, doubleConstant, Nat.pow_zero, Nat.pow_one]
  ac_rfl

theorem monomial_mono (k x : Nat) {p q : Profile}
    (bound : ∀ i, p.coefficient i ≤ q.coefficient i) :
    monomial k p x ≤ monomial k q x :=
  product_mono (k+1) (fun i _ => Nat.pow_le_pow_of_le_left (bound i) _)

structure Shape (k : Nat) (p : Profile) : Prop where
  positive : ∀ i, 0 < p.coefficient i
  above : ∀ i, k < i → p.coefficient i = 1
  constants : p.constant = true → ∀ i, 0 < i → p.coefficient i = 1
  zero : k = 0 → p.constant = true

structure Bound (k x : Nat) (p : Profile) (v : Nat) : Prop where
  shape : Shape k p
  lower : p.coefficient k ^ (x^k) ≤ v
  upper : v ≤ monomial k p x

theorem value_positive {k x v : Nat} {p : Profile} (h : Bound k x p v) : 0 < v :=
  Nat.lt_of_lt_of_le (Nat.pow_pos (h.shape.positive k)) h.lower

theorem constant_value {k x v : Nat} {p : Profile}
    (h : Bound k x p v) (constant : p.constant = true) :
    v ≤ p.coefficient 0 := by
  have same : monomial k p x = monomial k (fixed (p.coefficient 0)) x := by
    apply product_congr
    intro i _
    cases i with
    | zero => rfl
    | succ i => simp only [h.shape.constants constant (i+1) (by omega), fixed]
  have upper := h.upper
  rw [same, monomial_fixed] at upper
  exact upper

theorem shape_fixed (k b : Nat) (positive : 0 < b) : Shape k (fixed b) := by
  constructor
  · intro i; cases i <;> simp only [fixed] <;> omega
  · intro i hi; cases i <;> simp only [fixed]; omega
  · intro _ i hi; cases i <;> simp only [fixed]; omega
  · intro _; rfl

theorem shape_multiply {k : Nat} {p q : Profile} (hp : Shape k p) (hq : Shape k q) :
    Shape k (multiply p q) := by
  constructor
  · intro i; exact Nat.mul_pos (hp.positive i) (hq.positive i)
  · intro i hi; simp only [multiply, hp.above i hi, hq.above i hi, Nat.mul_one]
  · intro both i hi
    have flags : p.constant = true ∧ q.constant = true := by
      simpa only [multiply, Bool.and_eq_true] using both
    simp only [multiply, hp.constants flags.1 i hi, hq.constants flags.2 i hi, Nat.mul_one]
  · intro zero
    simp only [multiply, hp.zero zero, hq.zero zero, Bool.true_and]

theorem shape_power {k : Nat} {p : Profile} (hp : Shape k p) (e : Nat) :
    Shape k (power p e) := by
  constructor
  · intro i; exact Nat.pow_pos (hp.positive i)
  · intro i hi; simp only [power, hp.above i hi, Nat.one_pow]
  · intro flag i hi; simp only [power, hp.constants flag i hi, Nat.one_pow]
  · exact hp.zero

theorem shape_shift {k : Nat} {p : Profile} (hp : Shape k p) :
    Shape (k+1) (shift p) := by
  constructor
  · intro i
    cases i with
    | zero => exact Nat.zero_lt_one
    | succ i => exact hp.positive i
  · intro i hi
    cases i with
    | zero => omega
    | succ i => exact hp.above i (by omega)
  · intro flag i hi
    have flags : p.constant = true ∧ p.coefficient 0 = 1 := by
      simpa only [shift, Bool.and_eq_true, beq_iff_eq] using flag
    cases i with
    | zero => omega
    | succ i =>
      cases i with
      | zero => exact flags.2
      | succ i => exact hp.constants flags.1 (i+1) (by omega)
  · intro impossible; omega

theorem shape_add {k : Nat} {p q : Profile} (hp : Shape k p) (hq : Shape k q) :
    Shape k (add p q) := by
  unfold add
  split
  · exact shape_fixed k _ (by have := hp.positive 0; omega)
  · rename_i different
    constructor
    · intro i
      cases i with
      | zero =>
        exact Nat.mul_pos (by decide) (Nat.lt_of_lt_of_le (hp.positive 0) (Nat.le_max_left _ _))
      | succ i => exact Nat.lt_of_lt_of_le (hp.positive (i+1)) (Nat.le_max_left _ _)
    · intro i hi
      cases i with
      | zero => omega
      | succ i =>
        simp only [doubleConstant, maximum, hp.above (i+1) hi, hq.above (i+1) hi, Nat.max_self]
    · intro flag; contradiction
    · intro zero
      have flags : (p.constant && q.constant) = true := by rw [hp.zero zero, hq.zero zero]; rfl
      contradiction

theorem bound_fixed (k x b : Nat) (positive : 0 < b) :
    Bound k x (fixed b) b := by
  refine ⟨shape_fixed k b positive, ?_, ?_⟩
  · cases k with
    | zero => simp only [fixed, Nat.pow_zero, Nat.pow_one]; exact Nat.le_refl _
    | succ k => simpa only [fixed, Nat.one_pow] using positive
  · rw [monomial_fixed]
    exact Nat.le_refl _

theorem bound_multiply {k x a b : Nat} {p q : Profile}
    (hp : Bound k x p a) (hq : Bound k x q b) :
    Bound k x (multiply p q) (a*b) := by
  refine ⟨shape_multiply hp.shape hq.shape, ?_, ?_⟩
  · simpa only [multiply, Nat.mul_pow] using Nat.mul_le_mul hp.lower hq.lower
  · rw [monomial_multiply]; exact Nat.mul_le_mul hp.upper hq.upper

theorem bound_power {k x a : Nat} {p : Profile}
    (hp : Bound k x p a) (e : Nat) : Bound k x (power p e) (a^e) := by
  refine ⟨shape_power hp.shape e, ?_, ?_⟩
  · simpa only [power, Nat.pow_right_comm _ e] using Nat.pow_le_pow_of_le_left hp.lower e
  · rw [monomial_power]; exact Nat.pow_le_pow_of_le_left hp.upper e

theorem bound_shift {k x a : Nat} {p : Profile}
    (hp : Bound k x p a) : Bound (k+1) x (shift p) (a^x) := by
  refine ⟨shape_shift hp.shape, ?_, ?_⟩
  · simpa only [shift, Nat.pow_succ, Nat.pow_mul] using Nat.pow_le_pow_of_le_left hp.lower x
  · rw [monomial_shift]; exact Nat.pow_le_pow_of_le_left hp.upper x

theorem monomial_extend {k x : Nat} {p : Profile} (hp : Shape k p) :
    monomial (k+1) p x = monomial k p x := by
  simp only [monomial, product, hp.above (k+1) (by omega), Nat.one_pow, Nat.mul_one]

theorem bound_promote {k x a : Nat} {p : Profile} (hp : Bound k x p a) :
    Bound (k+1) x p a := by
  refine ⟨⟨hp.shape.positive, fun i hi => hp.shape.above i (by omega),
    hp.shape.constants, fun impossible => by omega⟩, ?_, ?_⟩
  · rw [hp.shape.above (k+1) (by omega), Nat.one_pow]
    exact value_positive hp
  · rw [monomial_extend hp.shape]; exact hp.upper

theorem bound_add {k x a b : Nat} {p q : Profile}
    (hp : Bound k x p a) (hq : Bound k x q b) :
    Bound k x (add p q) (a+b) := by
  refine ⟨shape_add hp.shape hq.shape, ?_, ?_⟩
  · unfold add
    split
    · cases k with
      | zero =>
        simpa only [fixed, Nat.pow_zero, Nat.pow_one] using Nat.add_le_add hp.lower hq.lower
      | succ k =>
        simp only [fixed, Nat.one_pow]
        have := value_positive hp
        omega
    · cases k with
      | zero =>
        rename_i flag
        have flags : (p.constant && q.constant) = true := by
          rw [hp.shape.zero rfl, hq.shape.zero rfl]; rfl
        contradiction
      | succ k =>
        change (max (p.coefficient (k+1)) (q.coefficient (k+1)))^(x^(k+1)) ≤ a+b
        rcases Nat.le_total (p.coefficient (k+1)) (q.coefficient (k+1)) with order | order
        · rw [Nat.max_eq_right order]
          exact Nat.le_trans hq.lower (by omega)
        · rw [Nat.max_eq_left order]
          exact Nat.le_trans hp.lower (by omega)
  · unfold add
    split
    · rename_i flags
      have both : p.constant = true ∧ q.constant = true := by
        simpa only [Bool.and_eq_true] using flags
      rw [monomial_fixed]
      exact Nat.add_le_add (constant_value hp both.1) (constant_value hq both.2)
    · rw [monomial_double]
      have left := Nat.le_trans hp.upper (monomial_mono k x
        (p := p) (q := maximum p q) (fun _ => Nat.le_max_left _ _))
      have right := Nat.le_trans hq.upper (monomial_mono k x
        (p := q) (q := maximum p q) (fun _ => Nat.le_max_right _ _))
      omega

-- Histories use the existing marked interpreter's newest-first addresses.
-- A free block adds t to its anchored square count; fixed blocks do not.
inductive Block
  | add (a b : Nat)
  | mul (a b : Nat)
  | fixed (a g : Nat)
  | free (a g : Nat)
  deriving Repr

def concrete (t : Nat) : Block → SolvedMarked.Instr
  | .add a b => .add a b
  | .mul a b => .mul a b
  | .fixed a g => .sqRun a g
  | .free a g => .sqRun a (g+t)

def freeBlock : Block → Nat
  | .free _ _ => 1
  | _ => 0

def freeCount : List Block → Nat
  | [] => 0
  | block::tail => freeBlock block + freeCount tail

def pushProfile (p : Profile) (history : Nat → Profile) : Nat → Profile
  | 0 => p
  | i+1 => history i

structure State where
  dimension : Nat
  history : Nat → Profile

def step (block : Block) (state : State) : State :=
  match block with
  | .add a b => ⟨state.dimension,
      pushProfile (add (state.history a) (state.history b)) state.history⟩
  | .mul a b => ⟨state.dimension,
      pushProfile (multiply (state.history a) (state.history b)) state.history⟩
  | .fixed a g => ⟨state.dimension,
      pushProfile (power (state.history a) (2^g)) state.history⟩
  | .free a g => ⟨state.dimension+1,
      pushProfile (shift (power (state.history a) (2^g))) state.history⟩

def build : List Block → State → State
  | [], state => state
  | block::tail, state => build tail (step block state)

def initial : State := ⟨0, fun _ => fixed 1⟩

def HistoryBound (x : Nat) (state : State) (actual : SolvedMarked.Hist) : Prop :=
  ∀ i, Bound state.dimension x (state.history i) (actual i)

theorem squares_power (g a : Nat) : SolvedMarked.iterSq g a = a^(2^g) := by
  induction g with
  | zero => simp only [SolvedMarked.iterSq, Nat.pow_zero, Nat.pow_one]
  | succ g ih =>
    simp only [SolvedMarked.iterSq, ih]
    calc
      a^(2^g)*a^(2^g) = a^(2^g+2^g) := (Nat.pow_add _ _ _).symm
      _ = a^(2^(g+1)) := by rw [Nat.pow_succ, Nat.mul_two]

theorem history_push {x v : Nat} {state : State} {actual : SolvedMarked.Hist}
    {p : Profile} (history : HistoryBound x state actual)
    (value : Bound state.dimension x p v) :
    HistoryBound x ⟨state.dimension, pushProfile p state.history⟩
      (SolvedMarked.push v actual) := by
  intro i
  cases i with
  | zero => exact value
  | succ i => exact history i

theorem history_promote {x : Nat} {state : State} {actual : SolvedMarked.Hist}
    (history : HistoryBound x state actual) :
    HistoryBound x ⟨state.dimension+1, state.history⟩ actual :=
  fun i => bound_promote (history i)

theorem step_bound (t : Nat) (block : Block) {state : State} {actual : SolvedMarked.Hist}
    (history : HistoryBound (2^t) state actual) :
    HistoryBound (2^t) (step block state)
      (SolvedMarked.evalI (concrete t block) actual) := by
  cases block with
  | add a b => exact history_push history (bound_add (history a) (history b))
  | mul a b => exact history_push history (bound_multiply (history a) (history b))
  | fixed a g =>
    simpa only [step, concrete, SolvedMarked.evalI, squares_power] using
      history_push history (bound_power (history a) (2^g))
  | free a g =>
    have next := history_push (history_promote history)
      (bound_shift (bound_power (history a) (2^g)))
    simpa only [step, concrete, SolvedMarked.evalI, squares_power, Nat.pow_add, Nat.pow_mul]
      using next

theorem build_bound (code : List Block) (t : Nat) {state : State} {actual : SolvedMarked.Hist}
    (history : HistoryBound (2^t) state actual) :
    HistoryBound (2^t) (build code state)
      (SolvedMarked.eval (code.map (concrete t)) actual) := by
  induction code generalizing state actual with
  | nil => exact history
  | cons block _tail ih => exact ih (step_bound t block history)

theorem step_dimension (block : Block) (state : State) :
    (step block state).dimension = state.dimension + freeBlock block := by
  cases block <;> rfl

theorem build_dimension (code : List Block) (state : State) :
    (build code state).dimension = state.dimension + freeCount code := by
  induction code generalizing state with
  | nil => rfl
  | cons block tail ih =>
    simp only [build, ih, freeCount, step_dimension, Nat.add_assoc]

theorem program_profile (code : List Block) (t : Nat) :
    Bound (freeCount code) (2^t) ((build code initial).history 0)
      (SolvedMarked.eval (code.map (concrete t)) (fun _ => 1) 0) := by
  have start : HistoryBound (2^t) initial (fun _ => 1) :=
    fun _ => bound_fixed 0 (2^t) 1 (by decide)
  have final := build_bound code t start 0
  simpa only [build_dimension, initial, Nat.zero_add] using final

theorem monomial_collect {k x : Nat} {p : Profile}
    (positive : 0 < x) (shape : Shape (k+1) p) :
    monomial (k+1) p x ≤
      (p.coefficient (k+1)^x * product (k+1) p.coefficient)^(x^k) := by
  have lower : product (k+1) (fun i => p.coefficient i^(x^i)) ≤
      (product (k+1) p.coefficient)^(x^k) := by
    rw [← product_power]
    apply product_mono
    intro i hi
    apply Nat.pow_le_pow_of_le_right (shape.positive i)
    exact Nat.pow_le_pow_of_le_right positive (by omega)
  have bound := Nat.mul_le_mul_right (p.coefficient (k+1)^(x^(k+1))) lower
  have leading : p.coefficient (k+1)^(x^(k+1)) =
      (p.coefficient (k+1)^x)^(x^k) := by
    rw [← Nat.pow_mul, Nat.pow_succ, Nat.mul_comm x]
  simpa only [monomial, product, leading, Nat.mul_pow, Nat.mul_comm] using bound

theorem index_below_power (t : Nat) : t < 2^t := by
  induction t with
  | zero => decide
  | succ t ih =>
    rw [Nat.pow_succ, Nat.mul_two]
    have := Nat.two_pow_pos t
    omega

def endpoint (code : List Block) (t : Nat) :=
  SolvedMarked.eval (code.map (concrete t)) (fun _ => 1) 0

def leading (code : List Block) :=
  ((build code initial).history 0).coefficient (freeCount code)

theorem diagonal_criterion (code : List Block) (v : Nat)
    (positive : 0 < v) (free : 0 < freeCount code) :
    (∃ t, endpoint code t ≤ v^((2^t)^(freeCount code))-1) ↔ leading code < v := by
  constructor
  · intro ⟨t,upper⟩
    apply Decidable.byContradiction
    intro notBelow
    have bound := program_profile code t
    have excludes := SolvedEffective.profile_lower_excludes positive
      (show v ≤ ((build code initial).history 0).coefficient (freeCount code) by
        change ¬leading code < v at notBelow; exact Nat.le_of_not_gt notBelow) bound.lower
    exact Nat.not_le_of_lt excludes upper
  · intro below
    let p := (build code initial).history 0
    let b := leading code
    let s := product (freeCount code) p.coefficient
    let t := b*s
    have bounds := program_profile code t
    have bpositive : 0 < b := bounds.shape.positive _
    have plenty : b*s ≤ 2^t := Nat.le_of_lt (index_below_power t)
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt free)
    have shape : Shape (k+1) p := by simpa only [hk] using bounds.shape
    have collected := monomial_collect (Nat.two_pow_pos t) shape
    have upper : endpoint code t ≤ (b^(2^t)*s)^((2^t)^k) := by
      have first : endpoint code t ≤ monomial (k+1) p (2^t) := by
        simpa only [hk] using bounds.upper
      have combined := Nat.le_trans first collected
      simpa only [b, s, leading, p, hk] using combined
    refine ⟨t,?_⟩
    have answer := SolvedEffective.profile_upper_witness bpositive below
      (Nat.two_pow_pos t) plenty upper
    simpa only [hk] using answer

theorem concrete_cost (code : List Block) (t : Nat) :
    SolvedInflation.cost (code.map (concrete t)) =
      SolvedInflation.cost (code.map (concrete 0)) + freeCount code * t := by
  induction code with
  | nil => simp only [List.map_nil, SolvedInflation.cost, freeCount, Nat.zero_mul]
  | cons block tail ih =>
    cases block <;> simp only [List.map_cons, concrete, SolvedInflation.cost,
      freeCount, freeBlock, ih, Nat.zero_add, Nat.zero_mul, Nat.one_mul,
      Nat.add_mul, Nat.add_zero] <;> omega

theorem diagonal_target (n t d : Nat) :
    (2^(2^n))^((2^t)^d) = 2^(2^(n+d*t)) := by
  rw [← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add]
  rw [Nat.mul_comm t d]

end SolvedProfiles
