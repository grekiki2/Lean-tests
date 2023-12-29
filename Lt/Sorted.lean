import Mathlib

-- Apparently a standard definition
def is_sorted : List Nat → Bool
| [] => true
| [_] => true
| x :: y :: ys => x <= y ∧ is_sorted (y :: ys)

-- I feel like this is a more natural definition
def is_sorted_2 (as : List Nat) : Prop :=
  let n := as.length
  ∀ (i j:Fin n), i < j → as.get i ≤ as.get j

-- Optimized version I'd like to prove equivalent
def is_sorted_3 (as : List Nat) : Prop :=
  let n := as.length
  ∀ (i:Fin n), (h:i.val+1 < n) → (as.get i ≤ as.get ⟨i.val+1, h⟩)

-- A computable version of is_sorted_3. I don't like it
def is_sorted_4 (as : List Nat) : Bool :=
  let n := List.length as
  List.all (List.range n) (λ i => if h:(i<n-1) then
    as.get ⟨i, by {rw [Nat.sub_one, Nat.lt_pred_iff_succ_lt] at h; exact Nat.lt_of_succ_lt h}⟩
    ≤
    as.get ⟨i+1, Nat.add_lt_of_lt_sub h⟩
  else True)

#eval is_sorted_4 (List.range 10000)
#eval is_sorted (List.range 10000)

theorem rangeIsSorted (n:Nat) : is_sorted_4 (List.range n) := by
  rw [is_sorted_4]
  unfold List.all
  have q:∀ (a :Nat), List.length (List.range a) = a := by simp
  simp [q]
  cases n with
  | zero =>
    simp
  | succ n' =>
    match List.range (Nat.succ n') with
    | [] =>
      simp
    | _::_ =>
      simp

theorem v3_equiv_v4 (as: List Nat): is_sorted_3 as = is_sorted_4 as := by
  rw [is_sorted_3, is_sorted_4]
  simp
  constructor
  · intro h x hx dummy
    specialize h ⟨x, hx⟩
    simp at h
    rw [Nat.sub_one, Nat.lt_pred_iff_succ_lt, ← Nat.add_one] at dummy
    specialize h dummy
    assumption
  · intro h idx hidx
    specialize h idx.val (Fin.prop idx) (Nat.lt_sub_of_add_lt hidx)
    assumption

theorem v2_equiv_v3: is_sorted_2 = is_sorted_3 := by
  funext as
  rw [is_sorted_2, is_sorted_3]
  simp
  constructor
  · intro h i hi
    specialize h i ⟨i+1, hi⟩ (by {
        rw [Fin.lt_def]
        simp
      })
    assumption
  · intro h i j hij
    -- This is the interesting proof state
    -- TODO: use smarter induction? j-i style? Feasible?
    induction as with
    | nil =>
      simp at i
      exfalso
      exact Nat.not_succ_le_zero _ i.is_lt
    | cons a as' ih =>
      specialize ih (by{
        intro idx pidx
        specialize h ⟨idx.val+1, Nat.lt.step pidx⟩ (Nat.add_lt_of_lt_sub pidx)
        simp at h
        assumption
      })
      match i with
      | ⟨0, h2⟩ =>
        simp at *
        unfold List.get
        match j with
        | ⟨0, h3⟩ =>
          exfalso
          exact LT.lt.false hij
        | ⟨j'+1, h3⟩ =>
          simp
          simp [List.length] at h3
          have q:0 < as'.length := Nat.zero_lt_of_lt h3
          specialize h 0 (Nat.add_lt_of_lt_sub q)
          simp at h
          apply Nat.le_trans h
          specialize ih ⟨0, q⟩ ⟨j', h3⟩
          simp at *
          cases j' with
          | zero =>
            rfl
          | succ j'' =>
            exact ih (Nat.succ_pos j'')
      | ⟨i'+1, h2⟩ =>
        simp
        match j with
        | ⟨0, h3⟩ =>
          exfalso
          exact Nat.not_succ_le_zero _ hij
        | ⟨j'+1, h3⟩ =>
          simp
          simp at hij
          specialize ih ⟨i',  by {
            rw [Nat.add_one, List.length, Nat.add_one] at h2; exact Nat.succ_lt_succ_iff.mp h2
          }⟩ ⟨j', by {
            rw [Nat.add_one, List.length, Nat.add_one] at h3; exact Nat.succ_lt_succ_iff.mp h3
          }⟩ hij
          assumption

theorem v1_equiv_v3 (as: List Nat): is_sorted as = is_sorted_3 as := by
  simp
  unfold is_sorted is_sorted_3
  induction as with
  | nil => simp
  | cons a as' ih =>
    cases as' with
    | nil => simp
    | cons a' as'' =>
      simp at ih ⊢
      cases as'' with
      | nil =>
        simp at ih ⊢
        constructor
        · intro h idx hidx
          unfold is_sorted at h
          simp at h
          match idx with
          | ⟨0, _⟩ => trivial
          | ⟨1, _⟩ => trivial
        · intro h
          unfold is_sorted
          simp
          specialize h ⟨0, by simp⟩ (by simp)
          simp at h
          exact h
      | cons a'' as''' =>
        simp at ih ⊢
        constructor
        · intro ⟨cmp_a_a', sorted⟩ idx hidx
          match idx with
          | ⟨0, h3⟩ => simp; assumption
          | ⟨idx'+1, h3⟩ =>
            simp
            simp [is_sorted] at sorted
            have ih := ih.mp sorted ⟨idx', Nat.succ_lt_succ_iff.mp h3⟩ (Nat.succ_lt_succ_iff.mp hidx)
            assumption
        · intro h
          unfold is_sorted
          simp
          have ih := ih.mpr
          have h2:= h ⟨0, by simp⟩ (by simp)
          simp at h2
          simp [h2]
          apply ih
          intro i hi
          specialize h ⟨i.val+1, Nat.lt.step hi⟩ (Nat.add_lt_of_lt_sub hi)
          simp at h
          assumption
