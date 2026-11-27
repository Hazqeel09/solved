import Mathlib.Tactic

/-!
# Masks of cells

A mask `L : List Bool` selects cells by index; positions past the end are unselected.
`runCells L ks path` replays the decisions of a search that visits the cells `ks` in order and
records the selected ones in `path`; when `ks` is a permutation of `0, …, N-1` it reaches `L`.
-/

namespace Solved.Cert

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

/-! ## Replaying a search -/

/-- The path a search over the cells `ks` reaches when it follows the mask `L`. -/
def runCells (L : List Bool) : List ℕ → List Bool → List Bool
  | [], path => path
  | k :: ks, path => runCells L ks (if bit L k then setBit path k else path)

theorem length_runCells (L : List Bool) (ks : List ℕ) (path : List Bool) :
    (runCells L ks path).length = path.length := by
  induction ks generalizing path with
  | nil => rfl
  | cons k ks ih => simp only [runCells]; split_ifs <;> simp [ih]

theorem bit_runCells (L : List Bool) (ks : List ℕ) (path : List Bool) {i : ℕ}
    (hi : i < path.length) :
    bit (runCells L ks path) i = (bit path i || (decide (i ∈ ks) && bit L i)) := by
  induction ks generalizing path with
  | nil => simp [runCells]
  | cons k ks ih =>
    simp only [runCells]
    split_ifs with hs
    · rw [ih _ (by simpa using hi), bit_setBit]
      by_cases hik : i = k
      · subst hik; simp [hs, hi]
      · have hne : (i == k) = false := by simpa using hik
        simp [hik, hne]
    · rw [ih _ hi]
      by_cases hik : i = k
      · subst hik; simp [hs]
      · simp [hik]

/-- Following a mask of length `N` over a permutation of `0, …, N-1` reaches the mask. -/
theorem runCells_perm {ks : List ℕ} {N : ℕ} (hperm : ks.Perm (List.range N)) {L : List Bool}
    (hL : L.length = N) : runCells L ks (List.replicate N false) = L := by
  refine bit_ext (by simp [length_runCells, hL]) fun i hi => ?_
  have hiN : i < N := by simpa [length_runCells] using hi
  rw [bit_runCells _ _ _ (by simpa using hiN)]
  simp [hperm.mem_iff, hiN]

end Solved.Cert
