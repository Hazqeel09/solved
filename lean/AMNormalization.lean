import BoundedControls

namespace SolvedNormalization
open SolvedCoverage SolvedEncoding

-- General positive addition-multiplication straight-line programs may repeat
-- values, use identities, and write values smaller than a previous output.
structure Program (length : Nat) where
  value : Nat → Nat
  left : Nat → Nat
  right : Nat → Nat
  isMul : Nat → Bool
  initial : value 0=1
  valid : ∀ i, 0<i → i≤length → left i<i ∧ right i<i ∧
    value i = if isMul i then value (left i)*value (right i)
      else value (left i)+value (right i)

theorem values_positive {r : Nat} (p : Program r) (i : Nat) (bound : i≤r) : 1≤p.value i := by
  induction i using Nat.strongInductionOn with
  | ind i ih =>
    by_cases zero : i=0
    · subst i; rw [p.initial]; exact Nat.le_refl _
    · obtain ⟨hl,hr,recipe⟩ := p.valid i (by omega) bound
      have left := ih (p.left i) hl (by omega)
      have right := ih (p.right i) hr (by omega)
      cases flag : p.isMul i
      · simp only [flag,Bool.false_eq_true,if_false] at recipe
        omega
      · simp only [flag,if_true] at recipe
        have product := Nat.mul_le_mul left right
        omega

def outputs {r : Nat} (p : Program r) : Nat → List Nat
  | 0 => []
  | k+1 => p.value (k+1)::outputs p k

def allValues {r : Nat} (p : Program r) : List Nat := 1::outputs p r

theorem outputs_length {r : Nat} (p : Program r) (k : Nat) : (outputs p k).length=k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [outputs,List.length_cons,ih]

theorem outputs_contains {r : Nat} (p : Program r) (k : Nat) {i : Nat}
    (positive : 0<i) (bound : i≤k) : p.value i ∈ outputs p k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases last : i=k+1
    · subst i; simp [outputs]
    · have earlier := ih (by omega)
      simp only [outputs,List.mem_cons]
      exact Or.inr earlier

theorem value_member {r : Nat} (p : Program r) (i : Nat) (bound : i≤r) :
    p.value i ∈ allValues p := by
  simp only [allValues,List.mem_cons]
  by_cases zero : i=0
  · subst i; exact Or.inl p.initial
  · exact Or.inr (outputs_contains p r (by omega) bound)

theorem outputs_member {r : Nat} (p : Program r) (k : Nat) {v : Nat}
    (member : v ∈ outputs p k) : ∃ i, 0<i ∧ i≤k ∧ p.value i=v := by
  induction k with
  | zero => cases member
  | succ k ih =>
    simp only [outputs,List.mem_cons] at member
    cases member with
    | inl eq => exact ⟨k+1,by omega,Nat.le_refl _,eq.symm⟩
    | inr earlier =>
      obtain ⟨i,pos,bd,eq⟩ := ih earlier
      exact ⟨i,pos,by omega,eq⟩

theorem member_positive {r : Nat} (p : Program r) {v : Nat}
    (member : v ∈ allValues p) : 1≤v := by
  simp only [allValues,List.mem_cons] at member
  cases member with
  | inl eq => omega
  | inr written =>
    obtain ⟨i,_pos,bound,eq⟩ := outputs_member p r written
    rw [← eq]
    exact values_positive p i bound

theorem smaller_recipe {r : Nat} (p : Program r) (i : Nat)
    (bound : i≤r) (large : 1<p.value i) :
    ∃ a b, a ∈ allValues p ∧ b ∈ allValues p ∧ a<p.value i ∧ b<p.value i ∧
      (p.value i=a+b ∨ p.value i=a*b) := by
  induction i using Nat.strongInductionOn with
  | ind i ih =>
    have positive : 0<i := by
      by_cases zero : i=0
      · subst i; rw [p.initial] at large; omega
      · omega
    obtain ⟨hl,hr,recipe⟩ := p.valid i positive bound
    have lp := values_positive p (p.left i) (by omega)
    have rp := values_positive p (p.right i) (by omega)
    cases flag : p.isMul i
    · simp only [flag,Bool.false_eq_true,if_false] at recipe
      exact ⟨p.value (p.left i),p.value (p.right i),value_member p _ (by omega),
        value_member p _ (by omega),by omega,by omega,Or.inl recipe⟩
    · simp only [flag,if_true] at recipe
      by_cases leftOne : p.value (p.left i)=1
      · have same : p.value i=p.value (p.right i) := by simpa only [leftOne,Nat.one_mul] using recipe
        rw [same]
        exact ih (p.right i) hr (by omega) (by omega)
      by_cases rightOne : p.value (p.right i)=1
      · have same : p.value i=p.value (p.left i) := by simpa only [rightOne,Nat.mul_one] using recipe
        rw [same]
        exact ih (p.left i) hl (by omega) (by omega)
      have leftGrowth := Nat.mul_le_mul_left (p.value (p.left i)) (show 2≤p.value (p.right i) by omega)
      have rightGrowth := Nat.mul_le_mul_right (p.value (p.right i)) (show 2≤p.value (p.left i) by omega)
      rw [Nat.mul_two] at leftGrowth
      exact ⟨p.value (p.left i),p.value (p.right i),value_member p _ (by omega),
        value_member p _ (by omega),by omega,by omega,Or.inr recipe⟩

theorem member_recipe {r : Nat} (p : Program r) {v : Nat}
    (member : v ∈ allValues p) (large : 1<v) :
    ∃ a b, a ∈ allValues p ∧ b ∈ allValues p ∧ a<v ∧ b<v ∧ (v=a+b ∨ v=a*b) := by
  simp only [allValues,List.mem_cons] at member
  cases member with
  | inl eq => omega
  | inr written =>
    obtain ⟨i,_pos,bound,eq⟩ := outputs_member p r written
    rw [← eq]
    exact smaller_recipe p i bound (by omega)

def extend {k : Nat} (c : Chain k) (a b v : Nat) (mul : Bool)
    (aBound : a≤k) (bBound : b≤k) (rises : c.value k<v)
    (recipe : v=if mul then c.value a*c.value b else c.value a+c.value b) : Chain (k+1) where
  value i := if i=k+1 then v else c.value i
  left i := if i=k+1 then a else c.left i
  right i := if i=k+1 then b else c.right i
  isMul i := if i=k+1 then mul else c.isMul i
  initial := by simp only [show ¬0=k+1 by omega,if_false,c.initial]
  increasing := by
    intro i j ij bound
    have iOld : i≠k+1 := by omega
    by_cases newest : j=k+1
    · subst j
      simp only [if_pos rfl,if_true,if_neg iOld]
      exact Nat.lt_of_le_of_lt (monotone c (by omega) (Nat.le_refl _)) rises
    · simp only [if_neg newest,if_neg iOld]
      exact c.increasing i j ij (by omega)
  valid := by
    intro i pos bound
    by_cases newest : i=k+1
    · subst i
      simp only [if_pos rfl,if_true,show ¬a=k+1 by omega,show ¬b=k+1 by omega,if_false]
      exact ⟨by omega,by omega,recipe⟩
    · obtain ⟨hl,hr,eq⟩ := c.valid i pos (by omega)
      simp only [if_neg newest,show ¬c.left i=k+1 by omega,
        show ¬c.right i=k+1 by omega,if_false]
      exact ⟨hl,hr,eq⟩

theorem extend_old {k : Nat} (c : Chain k) (a b v : Nat) (mul : Bool)
    (ha : a≤k) (hb : b≤k) (rises : c.value k<v)
    (recipe : v=if mul then c.value a*c.value b else c.value a+c.value b)
    (i : Nat) (bound : i≤k) : (extend c a b v mul ha hb rises recipe).value i=c.value i := by
  change (if i=k+1 then v else c.value i)=c.value i
  rw [if_neg (by omega)]

theorem extend_head {k : Nat} (c : Chain k) (a b v : Nat) (mul : Bool)
    (ha : a≤k) (hb : b≤k) (rises : c.value k<v)
    (recipe : v=if mul then c.value a*c.value b else c.value a+c.value b) :
    (extend c a b v mul ha hb rises recipe).value (k+1)=v := by
  change (if k+1=k+1 then v else c.value (k+1))=v
  rw [if_pos rfl]

theorem nat_min_choice (a b : Nat) : min a b=a ∨ min a b=b := by
  by_cases order : a≤b
  · exact Or.inl (Nat.min_eq_left order)
  · exact Or.inr (Nat.min_eq_right (by omega))

theorem least_candidate (values : List Nat) (head target : Nat)
    (existsValue : ∃ v, v ∈ values ∧ head<v ∧ v≤target) :
    ∃ v, v ∈ values ∧ head<v ∧ v≤target ∧
      ∀ w, w ∈ values → head<w → w≤target → v≤w := by
  let candidates := values.filter (fun v => decide (head<v ∧ v≤target))
  have nonempty : candidates≠[] := by
    obtain ⟨v,member,lower,upper⟩ := existsValue
    have present : v ∈ candidates := List.mem_filter.mpr ⟨member,by simp [lower,upper]⟩
    intro empty
    rw [empty] at present
    cases present
  cases chosen : candidates.minimum? with
  | none => exact False.elim (nonempty (List.minimum?_eq_none_iff.mp chosen))
  | some v =>
    have specification := (List.minimum?_eq_some_iff Nat.le_refl nat_min_choice
      (fun _ _ _ => Nat.le_min)).mp chosen
    have belongs : v ∈ values ∧ head<v ∧ v≤target := by
      simpa only [candidates,List.mem_filter,decide_eq_true_eq] using specification.1
    refine ⟨v,belongs.1,belongs.2.1,belongs.2.2,?_⟩
    intro w member lower upper
    exact specification.2 w (List.mem_filter.mpr ⟨member,by simp [lower,upper]⟩)



def seedChain : Chain 0 where
  value := fun _ => 1
  left := fun _ => 0
  right := fun _ => 0
  isMul := fun _ => false
  initial := rfl
  increasing := by intro i j order bound; omega
  valid := by intro i positive bound; omega

structure NormalState {r : Nat} (p : Program r) (target k : Nat) where
  chain : Chain k
  rest : List Nat
  budget : k+rest.length=r
  ceiling : chain.value k≤target
  seen : ∀ v, v ∈ allValues p → v≤chain.value k →
    ∃ i, i≤k ∧ chain.value i=v
  future : ∀ v, v ∈ allValues p → chain.value k<v → v≤target → v ∈ rest

def initial_state {r target : Nat} (p : Program r) (member : target ∈ allValues p) :
    NormalState p target 0 where
  chain := seedChain
  rest := outputs p r
  budget := by simp [outputs_length]
  ceiling := member_positive p member
  seen := by
    intro v mem upper
    have positive := member_positive p mem
    have eq : v=1 := by change v≤1 at upper; omega
    exact ⟨0,Nat.le_refl _,eq.symm⟩
  future := by
    intro v mem lower _upper
    change 1<v at lower
    simp only [allValues,List.mem_cons] at mem
    cases mem with
    | inl eq => omega
    | inr remaining => exact remaining

def appended_state {r target k : Nat} {p : Program r} (s : NormalState p target k)
    (a b v : Nat) (mul : Bool) (ha : a≤k) (hb : b≤k)
    (rises : s.chain.value k<v) (ceiling : v≤target)
    (least : ∀ w, w ∈ allValues p → s.chain.value k<w → w≤target → v≤w)
    (recipe : v=if mul then s.chain.value a*s.chain.value b else s.chain.value a+s.chain.value b)
    (after : List Nat) (removed : Remove v s.rest after) : NormalState p target (k+1) where
  chain := extend s.chain a b v mul ha hb rises recipe
  rest := after
  budget := by
    have before := s.budget
    have shorter := remove_length removed
    omega
  ceiling := by rw [extend_head]; exact ceiling
  seen := by
    intro w member upper
    rw [extend_head] at upper
    by_cases current : w=v
    · subst w
      exact ⟨k+1,Nat.le_refl _,extend_head _ _ _ _ _ _ _ _ _⟩
    · have earlier : w≤s.chain.value k := by
        by_cases lower : s.chain.value k<w
        · have contradiction := least w member lower (by omega)
          omega
        · omega
      obtain ⟨i,ibound,value⟩ := s.seen w member earlier
      refine ⟨i,by omega,?_⟩
      rw [extend_old _ _ _ _ _ _ _ _ _ i ibound]
      exact value
  future := by
    intro w member lower upper
    rw [extend_head] at lower
    exact remove_preserves removed (by omega) (s.future w member (by omega) upper)

theorem normal_step {r target k : Nat} {p : Program r} (s : NormalState p target k)
    (targetMember : target ∈ allValues p) (notDone : s.chain.value k ≠ target) :
    ∃ next : NormalState p target (k+1), next.rest.length<s.rest.length := by
  have headPositive : 1≤s.chain.value k := by
    have h := monotone s.chain (Nat.zero_le k) (Nat.le_refl k)
    rw [s.chain.initial] at h
    exact h
  have below : s.chain.value k<target := by have h := s.ceiling; omega
  obtain ⟨v,member,rises,ceiling,least⟩ := least_candidate (allValues p) (s.chain.value k) target
    ⟨target,targetMember,below,Nat.le_refl _⟩
  obtain ⟨av,bv,amember,bmember,alower,blower,recipe⟩ := member_recipe p member (by omega)
  have aEarlier : av≤s.chain.value k := by
    by_cases later : s.chain.value k<av
    · have h := least av amember later (by omega); omega
    · omega
  have bEarlier : bv≤s.chain.value k := by
    by_cases later : s.chain.value k<bv
    · have h := least bv bmember later (by omega); omega
    · omega
  obtain ⟨a,ha,avalue⟩ := s.seen av amember aEarlier
  obtain ⟨b,hb,bvalue⟩ := s.seen bv bmember bEarlier
  obtain ⟨after,removed⟩ := remove_exists (s.future v member rises ceiling)
  have shorter : after.length<s.rest.length := by have h := remove_length removed; omega
  cases recipe with
  | inl add =>
    have actual : v=s.chain.value a+s.chain.value b := by rw [avalue,bvalue]; exact add
    exact ⟨appended_state s a b v false ha hb rises ceiling least actual after removed,shorter⟩
  | inr mul =>
    have actual : v=s.chain.value a*s.chain.value b := by rw [avalue,bvalue]; exact mul
    exact ⟨appended_state s a b v true ha hb rises ceiling least actual after removed,shorter⟩

theorem finish_normalization {r target : Nat} (p : Program r)
    (member : target ∈ allValues p) :
    ∀ fuel k, ∀ s : NormalState p target k, s.rest.length=fuel →
      ∃ length, ∃ chain : Chain length, length≤r ∧ chain.value length=target := by
  intro fuel
  induction fuel using Nat.strongInductionOn with
  | ind fuel ih =>
    intro k s measured
    by_cases done : s.chain.value k=target
    · have budget := s.budget
      exact ⟨k,s.chain,by omega,done⟩
    · obtain ⟨next,smaller⟩ := normal_step s member done
      exact ih next.rest.length (by omega) (k+1) next rfl

theorem normalize {r : Nat} (p : Program r) :
    ∃ length, ∃ chain : Chain length, length≤r ∧ chain.value length=p.value r := by
  have member := value_member p r (Nat.le_refl _)
  exact finish_normalization p member _ 0 (initial_state p member) rfl

theorem eventual_program_gap (C : Nat) :
    ∃ threshold, ∀ n, threshold≤n → ∀ r, ∀ p : Program r,
      p.value r=2^(2^n)-1 → n+C<r := by
  obtain ⟨threshold,lower⟩ := SolvedBounded.eventual_chain_gap C
  refine ⟨threshold,?_⟩
  intro n above r p endpoint
  obtain ⟨length,chain,shorter,same⟩ := normalize p
  have cost := lower n above length chain (same.trans endpoint)
  omega

end SolvedNormalization
