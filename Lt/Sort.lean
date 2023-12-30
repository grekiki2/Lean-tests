import Lt.Sorted

def insertElemIntoSortedList (as: List Nat) (b: Nat) : List Nat :=
  match as with
  | [] => [b]
  | a::as' => if b<=a then b::a::as' else a::(insertElemIntoSortedList as' b)

#eval insertElemIntoSortedList [1, 3, 4, 8, 9] 10


theorem insertIntoSortedIsSorted (as: List Nat) (b:Nat) (h: is_sorted as):
  is_sorted (insertElemIntoSortedList as b) := by
  induction as with
  | nil => rfl
  | cons a as' ih =>
    unfold is_sorted at h
    match as' with
    | [] =>
      unfold is_sorted insertElemIntoSortedList insertElemIntoSortedList
      by_cases h2:b≤a
      · simp [h2]; unfold is_sorted; rfl
      · simp [h2]; unfold is_sorted; simp; exact Nat.le_of_not_ge h2
    | a'::as'' =>
      simp at h
      specialize ih h.right
      -- Tukaj smo stanje spravili na smiselno
      unfold insertElemIntoSortedList
      by_cases h2:b≤a
      · simp [h2]
        simp [is_sorted, h2, h.left, h.right]
      · simp [h2]
        have q:a≤b :=by exact Nat.le_of_not_ge h2
        unfold insertElemIntoSortedList at ih ⊢
        by_cases h3:b≤a'
        · simp [h3] at ih ⊢
          unfold is_sorted
          simp [q, ih]
        · simp [h3] at ih ⊢
          unfold is_sorted
          simp [h.left, ih]
