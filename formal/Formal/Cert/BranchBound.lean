import Formal.Cert.Table

/-!
# Branch and bound over subsets with polynomial interval bounds

A mask `L : List Bool` selects cells; cell `k` contributes the polynomial table `t k`, and the
energy of a mask is `∑ₑ |(∑_{k ∈ L} (t k)ₑ)(x)|`. `bnb` decides a cell at a time. At each node
it bounds every completion entrywise: a completion's entry lies between the current value plus
the sum of the negative parts and plus the sum of the positive parts of the undecided cells, so
its absolute value is at most the larger of the two endpoint absolute values. If that bound is
already below `target` for all `x ≥ 0` the subtree is closed; at a leaf a mask must either be
below `target` or be one of the `allowed` masks.

`bnb_sound` is the semantic statement, and `runPath_build` / `eval_runAcc_build` identify the
mask a choice sequence reaches when the cells are a permutation of `0, …, N-1`.
-/

namespace Solved.Cert

open Finset

/-! ## Masks -/

/-- Bit `k` of a mask; positions past the end are `false`. -/
def bit : List Bool → ℕ → Bool
  | [], _ => false
  | c :: _, 0 => c
  | _ :: L, k + 1 => bit L k

@[simp] theorem bit_nil (k : ℕ) : bit [] k = false := by cases k <;> rfl
@[simp] theorem bit_cons_zero (c : Bool) (L : List Bool) : bit (c :: L) 0 = c := rfl
@[simp] theorem bit_cons_succ (c : Bool) (L : List Bool) (k : ℕ) : bit (c :: L) (k + 1) = bit L k :=
  rfl

theorem bit_of_length_le {L : List Bool} {k : ℕ} (h : L.length ≤ k) : bit L k = false := by
  induction L generalizing k with
  | nil => simp
  | cons c L ih =>
    cases k with
    | zero => simp at h
    | succ k => simpa using ih (by simpa using h)

@[simp] theorem bit_replicate_false (N k : ℕ) : bit (List.replicate N false) k = false := by
  induction N generalizing k with
  | zero => simp
  | succ N ih => cases k <;> simp [List.replicate_succ, ih]

theorem bit_ext {L₁ L₂ : List Bool} (hl : L₁.length = L₂.length)
    (h : ∀ k < L₁.length, bit L₁ k = bit L₂ k) : L₁ = L₂ := by
  induction L₁ generalizing L₂ with
  | nil => cases L₂ with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons c L₁ ih =>
    cases L₂ with
    | nil => simp at hl
    | cons d L₂ =>
      have h0 := h 0 (by simp)
      simp only [bit_cons_zero] at h0
      rw [h0, ih (by simpa using hl) fun k hk => by simpa using h (k + 1) (by simpa using hk)]

/-- Set bit `k` (no change past the end). -/
def setBit : List Bool → ℕ → List Bool
  | [], _ => []
  | _ :: L, 0 => true :: L
  | c :: L, k + 1 => c :: setBit L k

@[simp] theorem length_setBit (L : List Bool) (k : ℕ) : (setBit L k).length = L.length := by
  induction L generalizing k with
  | nil => rfl
  | cons c L ih => cases k <;> simp [setBit, ih]

theorem bit_setBit (L : List Bool) (k i : ℕ) :
    bit (setBit L k) i = (bit L i || (i == k && decide (i < L.length))) := by
  induction L generalizing k i with
  | nil => simp [setBit]
  | cons c L ih =>
    cases k with
    | zero => cases i <;> simp [setBit]
    | succ k => cases i <;> simp [setBit, ih]

/-! ## Steps and their precomputed interval bounds -/

/-- One decision: the cell, its contribution table, and entrywise sums of the positive and
negative parts of the contributions of this and every later step. -/
structure Step where
  cell : ℕ
  tab : Table
  hi : Table
  lo : Table

/-- `hi` of the first step, `0` for no steps. -/
def hiOf : List Step → Table
  | [] => []
  | s :: _ => s.hi

/-- `lo` of the first step, `0` for no steps. -/
def loOf : List Step → Table
  | [] => []
  | s :: _ => s.lo

/-- The steps for cells with the given contribution tables, in order, with their bounds. -/
def build : List (ℕ × Table) → List Step
  | [] => []
  | (k, t) :: r =>
    let ss := build r
    { cell := k, tab := t
      hi := Table.add (Table.map UPoly.posPart t) (hiOf ss)
      lo := Table.add (Table.map UPoly.negPart t) (loOf ss) } :: ss

theorem map_cell_build (l : List (ℕ × Table)) : (build l).map Step.cell = l.map Prod.fst := by
  induction l with
  | nil => rfl
  | cons kt r ih => obtain ⟨k, t⟩ := kt; simp [build, ih]

/-- The table a mask accumulates along the steps. -/
def runAcc (L : List Bool) : List Step → Table → Table
  | [], acc => acc
  | s :: ss, acc => runAcc L ss (if bit L s.cell then Table.add acc s.tab else acc)

/-- The path (mask of decided cells) a mask reaches along the steps. -/
def runPath (L : List Bool) : List Step → List Bool → List Bool
  | [], path => path
  | s :: ss, path => runPath L ss (if bit L s.cell then setBit path s.cell else path)

/-- The selected contributions to entry `e` at `x`. -/
def chosen (L : List Bool) (ss : List Step) (e : ℕ) (x : ℤ) : ℤ :=
  (ss.map fun s => if bit L s.cell then UPoly.eval (s.tab.get e) x else 0).sum

theorem eval_runAcc (L : List Bool) (ss : List Step) (acc : Table) (e : ℕ) (x : ℤ) :
    UPoly.eval ((runAcc L ss acc).get e) x = UPoly.eval (acc.get e) x + chosen L ss e x := by
  induction ss generalizing acc with
  | nil => simp [runAcc, chosen]
  | cons s ss ih =>
    simp only [runAcc, ih, chosen, List.map_cons, List.sum_cons]
    split_ifs <;> (simp; try ring)

theorem build_bounds (l : List (ℕ × Table)) (L : List Bool) (e : ℕ) {x : ℤ} (hx : 0 ≤ x) :
    UPoly.eval ((loOf (build l)).get e) x ≤ chosen L (build l) e x ∧
      chosen L (build l) e x ≤ UPoly.eval ((hiOf (build l)).get e) x := by
  induction l with
  | nil => simp [build, loOf, hiOf, chosen]
  | cons kt r ih =>
    obtain ⟨k, t⟩ := kt
    simp only [build, loOf, hiOf, chosen, List.map_cons, List.sum_cons, Table.eval_get_add,
      Table.get_map UPoly.posPart rfl, Table.get_map UPoly.negPart rfl] at ih ⊢
    obtain ⟨ih₁, ih₂⟩ := ih
    constructor
    · refine add_le_add ?_ ih₁
      split_ifs
      · exact UPoly.negPart_le_eval _ hx
      · exact UPoly.eval_negPart_nonpos _ hx
    · refine add_le_add ?_ ih₂
      split_ifs
      · exact UPoly.eval_le_posPart _ hx
      · exact UPoly.eval_posPart_nonneg _ hx

/-! ## The checker -/

/-- `target - bound > 0` on `x ≥ 0`, certified by coefficients. -/
def below (target bound : UPoly) : Bool := UPoly.posCert (UPoly.add target (UPoly.neg bound))

theorem lt_of_below {target bound : UPoly} (h : below target bound = true) {x : ℤ} (hx : 0 ≤ x) :
    UPoly.eval bound x < UPoly.eval target x := by
  have := UPoly.eval_pos_of_posCert h hx
  simp only [UPoly.eval_add, UPoly.eval_neg] at this
  linarith

/-- Branch and bound over the undecided steps: every mask reaching a leaf has energy below
`target` or its path is `allowed`. -/
def bnb (target : UPoly) (allowed : List (List Bool)) : List Step → List Bool → Table → Bool
  | [], path, acc => below target (Table.bound acc) || allowed.contains path
  | s :: ss, path, acc =>
    below target (Table.bound2 (Table.add acc s.hi) (Table.add acc s.lo)) ||
      (bnb target allowed ss path acc &&
        bnb target allowed ss (setBit path s.cell) (Table.add acc s.tab))

theorem bnb_sound (target : UPoly) (allowed : List (List Bool)) (l : List (ℕ × Table))
    (path : List Bool) (acc : Table) (h : bnb target allowed (build l) path acc = true)
    (L : List Bool) {x : ℤ} (hx : 0 ≤ x) (m : ℕ) :
    runPath L (build l) path ∈ allowed ∨
      ∑ e ∈ range m, |UPoly.eval ((runAcc L (build l) acc).get e) x| < UPoly.eval target x := by
  induction l generalizing path acc with
  | nil =>
    simp only [build, bnb, Bool.or_eq_true, List.contains_iff_mem] at h
    rcases h with h | h
    · exact Or.inr ((Table.sum_abs_le_bound acc hx m).trans_lt (lt_of_below h hx))
    · exact Or.inl h
  | cons kt r ih =>
    obtain ⟨k, t⟩ := kt
    let s : Step :=
      { cell := k, tab := t
        hi := Table.add (Table.map UPoly.posPart t) (hiOf (build r))
        lo := Table.add (Table.map UPoly.negPart t) (loOf (build r)) }
    have hbuild : build ((k, t) :: r) = s :: build r := rfl
    have hb : ∀ e, UPoly.eval (s.lo.get e) x ≤ chosen L (s :: build r) e x ∧
        chosen L (s :: build r) e x ≤ UPoly.eval (s.hi.get e) x :=
      fun e => build_bounds ((k, t) :: r) L e hx
    rw [hbuild] at h ⊢
    simp only [bnb, Bool.or_eq_true, Bool.and_eq_true] at h
    rcases h with h | ⟨h₀, h₁⟩
    · refine Or.inr (lt_of_le_of_lt ?_ (lt_of_below h hx))
      refine (sum_le_sum fun e _ => ?_).trans (Table.sum_max_le_bound2 _ _ hx m)
      obtain ⟨hlo, hhi⟩ := hb e
      have e₁ := Table.eval_get_add acc s.lo e x
      have e₂ := Table.eval_get_add acc s.hi e x
      have e₃ := eval_runAcc L (s :: build r) acc e x
      rw [max_comm]
      exact abs_le_max_abs_abs (by linarith) (by linarith)
    · simp only [runPath, runAcc]
      split_ifs
      · exact ih _ _ h₁
      · exact ih _ _ h₀

/-! ## Reaching every mask -/

theorem length_runPath (L : List Bool) (ss : List Step) (path : List Bool) :
    (runPath L ss path).length = path.length := by
  induction ss generalizing path with
  | nil => rfl
  | cons s ss ih => simp only [runPath]; split_ifs <;> simp [ih]

theorem bit_runPath (L : List Bool) (ss : List Step) (path : List Bool) {i : ℕ}
    (hi : i < path.length) :
    bit (runPath L ss path) i = (bit path i || (decide (i ∈ ss.map Step.cell) && bit L i)) := by
  induction ss generalizing path with
  | nil => simp [runPath]
  | cons s ss ih =>
    simp only [runPath]
    split_ifs with hs
    · rw [ih _ (by simpa using hi), bit_setBit]
      by_cases his : i = s.cell
      · subst his; simp [hs, hi]
      · have hne : (i == s.cell) = false := by simpa using his
        simp [his, hne]
    · rw [ih _ hi]
      by_cases his : i = s.cell
      · subst his; simp [hs]
      · simp [his]

/-- If the cells are a permutation of `0, …, N-1`, the mask of length `N` reaches itself. -/
theorem runPath_build (l : List (ℕ × Table)) {N : ℕ}
    (hperm : (l.map Prod.fst).Perm (List.range N)) {L : List Bool} (hL : L.length = N) :
    runPath L (build l) (List.replicate N false) = L := by
  refine bit_ext (by simp [length_runPath, hL]) fun i hi => ?_
  have hiN : i < N := by simpa [length_runPath] using hi
  rw [bit_runPath _ _ _ (by simpa using hiN)]
  simp [map_cell_build, hperm.mem_iff, hiN]

theorem chosen_build (L : List Bool) (l : List (ℕ × Table)) (e : ℕ) (x : ℤ) :
    chosen L (build l) e x =
      (l.map fun kt => if bit L kt.1 then UPoly.eval (kt.2.get e) x else 0).sum := by
  induction l with
  | nil => rfl
  | cons kt r ih =>
    obtain ⟨k, t⟩ := kt
    simp only [build, chosen, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- The accumulated value of a mask, for cells forming a permutation of `0, …, N-1`. -/
theorem eval_runAcc_build (L : List Bool) (ks : List ℕ) (T : ℕ → Table) {N : ℕ}
    (hperm : ks.Perm (List.range N)) (e : ℕ) (x : ℤ) :
    UPoly.eval ((runAcc L (build (ks.map fun k => (k, T k))) []).get e) x =
      ∑ k ∈ range N, if bit L k then UPoly.eval ((T k).get e) x else 0 := by
  rw [eval_runAcc, chosen_build, List.map_map]
  simp only [Table.get_nil, UPoly.eval_nil, zero_add, Function.comp_def]
  rw [(hperm.map _).sum_eq]
  rfl

end Solved.Cert
