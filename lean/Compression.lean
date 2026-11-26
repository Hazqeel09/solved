import Lean

/- The C12 ordinary interval: every primitive multiplication refers to the
   most recent q values. A square block may have extra iterations only if it
   already contains q squares. No arithmetic library beyond Lean core. -/
namespace SolvedCompression

abbrev Hist := Nat → Nat

def iterSq : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => iterSq n x * iterSq n x

theorem iterSq_mul (n x y : Nat) : iterSq n (x*y) = iterSq n x * iterSq n y := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [iterSq, ih]; ac_rfl

theorem iterSq_add (e f x : Nat) : iterSq (e+f) x = iterSq f (iterSq e x) := by
  induction f with
  | zero => rfl
  | succ f ih =>
    change iterSq (e+f) x * iterSq (e+f) x = iterSq f (iterSq e x) * iterSq f (iterSq e x)
    rw [ih]

def push (v : Nat) (w : Hist) : Hist
  | 0 => v
  | i+1 => w i

def tick (w : Hist) : Hist := push (w 0 * w 0) w

def squares : Nat → Hist → Hist
  | 0, w => w
  | k+1, w => tick (squares k w)

def multiply {q : Nat} (a b : Fin q) (w : Hist) : Hist :=
  push (w a * w b) w

def Agrees (q e : Nat) (large small : Hist) : Prop :=
  ∀ i, i < q → large i = iterSq e (small i)

theorem head_squares (k : Nat) (w : Hist) : squares k w 0 = iterSq k (w 0) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [squares,tick,push,iterSq,ih]

theorem scale_mul {q e : Nat} {large small : Hist} (h : Agrees q e large small)
    (a b : Fin q) : Agrees q e (multiply a b large) (multiply a b small) := by
  intro i hi
  cases i with
  | zero => simp only [multiply,push,iterSq_mul,h a.val a.isLt,h b.val b.isLt]
  | succ j => exact h j (by omega)

theorem scale_tick {q e : Nat} {large small : Hist} (h : Agrees q e large small) :
    Agrees q e (tick large) (tick small) := by
  intro i hi
  cases i with
  | zero => simp only [tick,push,iterSq_mul,h 0 hi]
  | succ j => exact h j (by omega)

theorem scale_squares {q e : Nat} {large small : Hist} (h : Agrees q e large small)
    (k : Nat) : Agrees q e (squares k large) (squares k small) := by
  induction k with
  | zero => exact h
  | succ k ih => exact scale_tick ih

theorem reset_squares (q ex : Nat) (w : Hist) :
    Agrees q ex (squares (q+ex) w) (squares q w) := by
  induction q with
  | zero => intro i hi; omega
  | succ q ih =>
    intro i hi
    cases i with
    | zero => simp only [head_squares,iterSq_add]
    | succ j =>
      simpa only [Nat.succ_add,squares,tick,push] using ih j (by omega)

inductive Block (q : Nat)
  | sq (keep ex : Nat)
  | mul (a b : Fin q)

def Good {q : Nat} : Block q → Prop
  | .sq keep ex => ex = 0 ∨ keep = q
  | .mul _ _ => True

def extra {q : Nat} : Block q → Nat
  | .sq _ ex => ex
  | .mul _ _ => 0

def applyBlock {q : Nat} (full : Bool) : Block q → Hist → Hist
  | .sq keep ex, w => squares (if full then keep+ex else keep) w
  | .mul a b, w => multiply a b w

theorem block_correct {q e : Nat} {large small : Hist}
    (b : Block q) (ok : Good b) (h : Agrees q e large small) :
    Agrees q (e + extra b) (applyBlock true b large) (applyBlock false b small) := by
  cases b with
  | mul a b => exact scale_mul h a b
  | sq keep ex =>
    rcases ok with he | hk
    · subst ex; exact scale_squares h keep
    · subst keep
      intro i hi
      change squares (q+ex) large i = iterSq (e+ex) (squares q small i)
      rw [scale_squares h (q+ex) i hi, reset_squares q ex small i hi]
      rw [Nat.add_comm e ex, iterSq_add]

def execute {q : Nat} (full : Bool) : List (Block q) → Hist → Hist
  | [], w => w
  | b::bs, w => execute full bs (applyBlock full b w)

def extras {q : Nat} : List (Block q) → Nat
  | [] => 0
  | b::bs => extra b + extras bs

theorem ordinary_correct {q : Nat} (bs : List (Block q))
    (ok : ∀ b ∈ bs, Good b) (e : Nat) (large small : Hist) (h : Agrees q e large small) :
    Agrees q (e + extras bs) (execute true bs large) (execute false bs small) := by
  induction bs generalizing e large small with
  | nil => exact h
  | cons b bs ih =>
    have hb := block_correct b (ok b (by simp)) h
    have ht : ∀ x ∈ bs, Good x := by
      intro x hx
      exact ok x (by simp [hx])
    simpa only [execute,extras,Nat.add_assoc] using ih ht (e+extra b) _ _ hb

#print axioms ordinary_correct
end SolvedCompression
