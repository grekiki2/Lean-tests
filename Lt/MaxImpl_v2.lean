import Lt.Mx

def maxOfListAux (as: List Nat) (curr: Nat) : Nat :=
  match as with
  | [] => curr
  | a::as' => maxOfListAux (as') (mx a curr)

def maxOfListAuxGeCurr (as:List Nat) (curr: Nat) : curr ≤ maxOfListAux as curr := by
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

def maxOfListMoreCurrIsHigher (as:List Nat)  : a ≤ b → maxOfListAux as a ≤ maxOfListAux as b := by
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

def maxBiggerThanFirstOfList (as:List Nat) (h: as.length>0) : maxOfList as h ≥ List.get as ⟨0, h⟩  := by
  cases as with
  | nil =>
    rw [List.length] at h
    exact False.elim ((Nat.not_lt_zero 0) h)
  | cons a as' =>
    rw [List.get, maxOfList]
    simp
    exact maxOfListAuxGeCurr _ _

def maxBiggerThanFirst (ar:Array Nat) (h: ar.size>0) : maxElement ar h ≥ ar.get ⟨0, h⟩ := by
  apply maxBiggerThanFirstOfList ar.data h

def maxBiggerThanIthOfList (as:List Nat) (h: as.length>0) (idx: Fin as.length) : maxOfList as h ≥ List.get as idx  := by
  induction as with
  | nil =>
    rw [List.length] at h
    exact False.elim ((Nat.not_lt_zero 0) h)
  | cons a as' ih =>
    match idx with
    | ⟨0, _⟩ => exact maxBiggerThanFirstOfList (a::as') (Nat.succ_pos _)
    | ⟨Nat.succ b, ihh⟩ =>
      simp [maxOfList, List.get]
      have h2: List.length as' > b := by {
        rw [List.length, Nat.add_one] at ihh
        exact Nat.lt_of_succ_lt_succ ihh
      }
      have h3: List.length as' > 0 := (Nat.zero_lt_of_lt h2)
      specialize ih h3 ⟨b, h2⟩
      cases as' with
      | nil =>
        simp [List.length] at ihh
        have q:= Nat.le_of_lt_succ ihh
        exact False.elim (Nat.not_succ_le_zero b q)
      | cons a' as'' =>
        unfold maxOfList at ih
        simp at ih
        unfold maxOfListAux
        have q:= maxOfListMoreCurrIsHigher as'' (mx_bigger_than_fst a' a)
        exact Nat.le_trans ih q

def maxBiggerThanAll (ar:Array Nat) (h: ar.size>0) : ∀ idx:Fin ar.size, maxElement ar h ≥ ar.get idx := by
  intro idx
  rw [Array.get, maxElement]
  apply maxBiggerThanIthOfList (ar.data) h idx
