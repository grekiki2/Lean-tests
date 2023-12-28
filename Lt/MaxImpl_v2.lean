import Mathlib
import Lt.Mx

def maxOfListAux (as: List Nat) (curr: Nat) : Nat :=
  match as with
  | [] => curr
  | a::as' => maxOfListAux (as') (mx a curr)

theorem maxOfListAuxGeCurr (as:List Nat) (curr: Nat) : curr ≤ maxOfListAux as curr := by
  induction as generalizing curr with
  | nil =>
    simp [maxOfListAux]
  | cons a as' ih =>
    simp [maxOfListAux]
    by_cases cmp: a≥curr
    · rw [mx_takes_bigger cmp]
      specialize ih a
      exact Nat.le_trans cmp ih
    · have q:= Nat.gt_of_not_le cmp
      rw [mx_symm, mx_takes_gt q]
      exact ih curr

theorem maxOfListMoreCurrIsHigher (as:List Nat)  : a ≤ b → maxOfListAux as a ≤ maxOfListAux as b := by
  intro a_le_b
  induction as generalizing a b with
    unfold maxOfListAux
  | nil => assumption
  | cons a' as' ih =>
    suffices h: mx a' a ≤ mx a' b from ( by {exact ih h})
    rw [mx_symm, @mx_symm a' b]
    exact ge_increases_mx b a a' a_le_b

def maxOfList (as: List Nat) (h: as.length > 0) : Nat :=
  match as with
  | [] => False.elim (by {
    exact (Nat.not_lt_zero 0) h -- No idea why this works
  })
  | a::b => maxOfListAux b a

def maxElement (ar : Array Nat) (h: ar.size > 0) : Nat :=
  maxOfList ar.data h

#eval maxElement #[11, 20, 3, 4, 5] (by {
  rw [Array.size] -- Can we move further?
  exact Nat.succ_pos 4
})

theorem maxOfList_returns_maximum (as : List Nat) (h : as.length > 0) :
  ∀ (y : Nat), y ∈ as → y ≤ maxOfList as h := by
  intro y y_in_as
  induction as with
  | nil => exact False.elim (Nat.not_lt_zero 0 h)
  | cons a as' ih =>
    cases as' with
    | nil =>
      simp [maxOfList, maxOfListAux]
      simp at y_in_as
      rw [y_in_as]
    | cons a' as'' =>
      simp at y_in_as
      simp [maxOfList, maxOfListAux] at *
      match y_in_as with
      | Or.inl h2 =>
        rw [h2]
        have hyp :maxOfListAux as'' a ≤ maxOfListAux as'' (mx a' a) := by {
          rw [mx_symm]
          apply maxOfListMoreCurrIsHigher as'' (mx_bigger_than_fst a a')
        }
        exact Nat.le_trans (maxOfListAuxGeCurr as'' a) hyp
      | Or.inr h2 =>
        specialize ih h2
        have hyp :maxOfListAux as'' a' ≤ maxOfListAux as'' (mx a' a) := maxOfListMoreCurrIsHigher as'' (mx_bigger_than_fst a' a)
        exact Nat.le_trans ih hyp
