import Mathlib

def reverse (as: List Nat) : List Nat :=
  match as with
  | [] => []
  | a::as' => reverse as' ++ [a]

def aux_reverse (as tmp: List Nat) : List Nat :=
  match as with
  | [] => tmp
  | a::as' => aux_reverse as' (a::tmp)

theorem aux_reverse_simp (as tmp tail: List Nat): aux_reverse as tmp ++ tail = aux_reverse as (tmp++tail) := by
  induction as generalizing tmp with
  | nil => rfl
  | cons a as' ih =>
    unfold aux_reverse
    specialize ih (a::tmp)
    exact ih

-- Tail recursive
def reverse2 (as: List Nat) :=
  aux_reverse as []

#eval reverse (List.range 100)
#eval reverse2 (List.range 100)

-- Quite standard proof I think, similar to tutorials, needs aux function
theorem rev_equiv (as: List Nat): reverse as = reverse2 as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    unfold reverse reverse2
    rw [ih]
    apply aux_reverse_simp

theorem rev_add (as bs:List Nat): reverse2 (as++bs) = reverse2 bs ++ reverse2 as := by
  unfold reverse2
  induction as generalizing bs with
  | nil =>
    simp [aux_reverse]
  | cons a as' ih =>
    match bs with
    | [] =>
      simp [aux_reverse]
    | b::bs' =>
      have q: a::as'++b::bs'=a::(as'++b::bs') := by simp
      rw [q]
      unfold aux_reverse
      have q2:[]++[a]=[a] := by rfl
      rw [← q2,← aux_reverse_simp, ih, ← aux_reverse_simp]
      simp [aux_reverse]

-- I'm quite sure I have too many lines here
theorem rev_involution (as: List Nat): reverse2 (reverse2 as) = as := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    unfold reverse2 at ih ⊢
    match h:(aux_reverse (a :: as') []) with
    | [] =>
      unfold aux_reverse at h ⊢
      simp
      have q:[]++[a]=[a] := by rfl
      rw [← q, ← aux_reverse_simp] at h
      simp at h -- thanks Mathlib
    | b::b' =>
      unfold aux_reverse at h
      have q:[]++[a]=[a] := by rfl
      -- So many rw's below :P
      rw [← q] at h
      rw [← aux_reverse_simp] at h
      have h2:= congrArg reverse2 h -- This is neat
      rw [rev_add] at h2
      unfold reverse2 at h2
      rw [ih] at h2
      rw [aux_reverse, aux_reverse] at h2
      rw [← h] at h2 ⊢
      rw [← h2]
      simp
