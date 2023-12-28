import Mathlib
import Lt.Mx

def maxOfList (as : List Nat) (h: as.length > 0) : Nat := Id.run do
  let mut m := as.head (by {
    match as with
    | [] => contradiction
    | a::as => simp
  })

  for a in as do
    m ← if a > m then a else m
  m

#eval maxOfList [1,2,3] (by simp [List.length, Nat.add_one])


theorem maxOfList_returns_maximum (as : List Nat) (h : as.length > 0) : ∀ (y : Nat), y ∈ as → y ≤ maxOfList as h := by
  intro y y_in_as
  unfold maxOfList
  simp
  unfold Id.run
  induction as with
  | nil => contradiction
  | cons a as' ih =>
    simp
    have q: ¬(a > List.head (a :: as') (by simp)) := by {
      intro h
      rw [List.head] at h
      simp at h
    }
    simp [q, List.head]
    cases as' with
    | nil =>
      simp at y_in_as ⊢
      exact Nat.le_of_eq y_in_as
    | cons a' as'' =>
      have trivial: List.length (a' :: as'')>0 := by simp
      specialize ih trivial
      simp at ih y_in_as
      match y_in_as with
      | Or.inl ih2 =>
        rw [ih2, forIn]
        unfold List.instForInList
        simp
        sorry
      | Or.inr ih2 =>
        specialize ih ih2
        rw [forIn] at ih ⊢
        unfold List.instForInList at ih ⊢
        simp at ih ⊢
        sorry
