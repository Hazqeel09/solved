import Lean

namespace SolvedDirected

def Ordered (negative : Bool) (f : Nat → Nat) : Prop :=
  if negative then ∀ a b, a ≤ b → f b ≤ f a
  else ∀ a b, a ≤ b → f a ≤ f b

theorem compose_order (s t : Bool) (f g : Nat → Nat)
    (hf : Ordered s f) (hg : Ordered t g) :
    Ordered (if s then !t else t) (fun x => g (f x)) := by
  cases s <;> cases t <;> simp only [Ordered, Bool.false_eq_true, if_false,
    if_true, Bool.not_false, Bool.not_true] at * <;>
    intro a b h <;> exact hg _ _ (hf _ _ h)

inductive Path {α : Type} (R : α → α → (Nat → Nat) → Bool → Prop) : α → α → Type
  | nil (v : α) : Path R v v
  | cons {u v w : α} (f : Nat → Nat) (sign : Bool) (edge : R u v f sign)
      (tail : Path R v w) : Path R u w

def run {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop} {u v : α} :
    Path R u v → Nat → Nat
  | .nil _, x => x
  | .cons f _ _ tail, x => run tail (f x)

def negative {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop} {u v : α} :
    Path R u v → Bool
  | .nil _ => false
  | .cons _ sign _ tail => if sign then !negative tail else negative tail

def Consistent {α : Type} (R : α → α → (Nat → Nat) → Bool → Prop)
    (values : α → Nat) : Prop :=
  ∀ u v f sign, R u v f sign → values v = f (values u)

theorem run_order {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop}
    (ordered : ∀ u v f sign, R u v f sign → Ordered sign f)
    {u v : α} (path : Path R u v) : Ordered (negative path) (run path) := by
  induction path with
  | nil v => simp only [negative, Ordered, Bool.false_eq_true, if_false, run]; intro a b h; exact h
  | cons f sign edge tail ih =>
    exact compose_order sign (negative tail) f (run tail) (ordered _ _ _ _ edge) ih

theorem run_realizes {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop}
    {values : α → Nat} (valid : Consistent R values) {u v : α} (path : Path R u v) :
    run path (values u) = values v := by
  induction path with
  | nil v => rfl
  | cons f sign edge tail ih =>
    simp only [run]
    rw [← valid _ _ f sign edge]
    exact ih

theorem agreement_along_path {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop}
    {x y : α → Nat} (cx : Consistent R x) (cy : Consistent R y)
    {u v : α} (path : Path R u v) (same : x u = y u) : x v = y v := by
  rw [← run_realizes cx path, ← run_realizes cy path, same]

theorem negative_closed_agreement {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop}
    (ordered : ∀ u v f sign, R u v f sign → Ordered sign f)
    {x y : α → Nat} (cx : Consistent R x) (cy : Consistent R y)
    {root : α} (path : Path R root root) (neg : negative path = true) :
    x root = y root := by
  have anti := run_order ordered path
  rw [neg] at anti
  simp only [Ordered, if_true] at anti
  have fx := run_realizes cx path
  have fy := run_realizes cy path
  by_cases xy : x root ≤ y root
  · have reverse := anti (x root) (y root) xy
    rw [fx,fy] at reverse
    exact Nat.le_antisymm xy reverse
  · have yx : y root ≤ x root := by omega
    have reverse := anti (y root) (x root) yx
    rw [fx,fy] at reverse
    exact Nat.le_antisymm reverse yx

def Fits {α : Type} (anchors : α → Option Nat) (values : α → Nat) : Prop :=
  ∀ v c, anchors v = some c → values v = c

def Covered {α : Type} (R : α → α → (Nat → Nat) → Bool → Prop)
    (anchors : α → Option Nat) : Prop :=
  ∀ v, ∃ root, ∃ _path : Path R root v,
    (∃ c, anchors root = some c) ∨ ∃ closed : Path R root root, negative closed = true

theorem unique_assignment {α : Type} {R : α → α → (Nat → Nat) → Bool → Prop}
    (ordered : ∀ u v f sign, R u v f sign → Ordered sign f)
    (anchors : α → Option Nat) (covered : Covered R anchors)
    {x y : α → Nat} (cx : Consistent R x) (cy : Consistent R y)
    (ax : Fits anchors x) (ay : Fits anchors y) : x = y := by
  funext v
  obtain ⟨root,path,seed⟩ := covered v
  apply agreement_along_path cx cy path
  cases seed with
  | inl anchored =>
    obtain ⟨c,hc⟩ := anchored
    exact (ax root c hc).trans (ay root c hc).symm
  | inr cycled =>
    obtain ⟨closed,neg⟩ := cycled
    exact negative_closed_agreement ordered cx cy closed neg

end SolvedDirected
