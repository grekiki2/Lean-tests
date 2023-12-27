#check Nat.max

def maxOfListAux (as: List Nat) (h: as.length > 0) (curr: Nat) : Nat :=
  match as with
  | [] => absurd h (λ h2 => by {
    rw [List.length] at h
    exact (Nat.not_lt_zero 0) h
  })
  | [a] => if a > curr then a else curr
  | a::b::as' => let curr2 := if a > curr then a else curr; maxOfListAux (b::as') (by {
    rw [List.length, Nat.add_one]
    exact Nat.succ_pos (List.length as')
   }) curr2

def maxOfListAuxGeCurr (as:List Nat) (h: as.length > 0) (curr: Nat) : curr ≤ maxOfListAux as h curr := by
  induction as generalizing curr with
  | nil => {
    apply False.elim
    rw [List.length] at h
    exact (Nat.not_lt_zero 0) h
  }
  | cons a as' ih => {
    cases as' with
    | nil => {
      rw [maxOfListAux]
      by_cases h2: (a>curr)
      · simp [h2]
        apply Nat.le_of_lt
        assumption
      · rw [if_neg h2]
        have q: curr = curr := by {
          exact Eq.refl curr
        }
        exact Nat.le_of_eq q
    }
    | cons a' as'' => {
      suffices List.length (a' :: as'') > 0 from (by {
        rw [maxOfListAux]
        by_cases h2: (a>curr)
        · simp [h2, ih]
          specialize ih this a
          calc curr
          _ ≤ a := by exact Nat.le_of_lt h2
          _ ≤  maxOfListAux (a' :: as'') (_ : List.length (a' :: as'') > 0) a := by assumption
        · simp [h2, ih, this]
      })
      rw [List.length, Nat.add_one]
      exact Nat.succ_pos _
    }
  }

def maxOfListMoreCurrIsHigher (as:List Nat) (h: as.length > 0) : a ≤ b → maxOfListAux as h a ≤ maxOfListAux as h b := by
  intro a_le_b
  induction as generalizing a b with
  | nil => {
    apply False.elim
    rw [List.length] at h
    exact (Nat.not_lt_zero 0) h
  }
  | cons a' as' ih => {
    cases as' with
    | nil => {
      rw [maxOfListAux, maxOfListAux]
      by_cases h2: (a'>a)
      · simp [h2]
        by_cases h3: (a'>b)
        · simp [h3]
        · simp [h3]
          rw [← Nat.not_gt_eq]
          assumption
      · simp [h2]
        rw [Nat.not_gt_eq] at h2
        by_cases h3: (a'>b)
        · simp [h3]
          exact Nat.le_trans a_le_b (Nat.le_of_lt h3)
        · simp [h3]
          assumption
    }
    | cons a'' as'' => {
      rw [maxOfListAux, maxOfListAux]
      simp
      suffices (if a' > a then a' else a) ≤ (if a' > b then a' else b) from ( by {
        exact ih (by {rw [List.length, Nat.add_one]; exact Nat.succ_pos _}) this
      })
      by_cases h2: (a'>a)
      · simp [h2]
        by_cases h3: (a'>b)
        · simp [h3]
        · simp [h3]
          rw [← Nat.not_gt_eq]
          assumption
      · simp [h2]
        rw [Nat.not_gt_eq] at h2
        by_cases h3: (a'>b)
        · simp [h3]
          exact Nat.le_trans a_le_b (Nat.le_of_lt h3)
        · simp [h3]
          assumption
    }
  }

def maxOfList (as: List Nat) (h: as.length > 0) : Nat :=
  match as with
  | [] => False.elim (by {
    rw [List.length] at h
    exact (Nat.not_lt_zero 0) h
  })
  | a::b => maxOfListAux (a::b) h a

def maxElement (ar : Array Nat) (h: ar.size > 0) : Nat :=
  maxOfList ar.data h

#eval maxElement #[11, 20, 3, 4, 5] (by {
  rw [Array.size] -- Can we move further?
  exact Nat.succ_pos 4
})

def maxBiggerThanFirstOfList (as:List Nat) (h: as.length>0) : maxOfList as h ≥ List.get as ⟨0, h⟩  := by
  cases as with
  | nil => {
    rw [List.length] at h
    exact False.elim ((Nat.not_lt_zero 0) h)
  }
  | cons a as' => {
    rw [List.get, maxOfList]
    simp
    exact maxOfListAuxGeCurr _ _ _
  }

def maxBiggerThanFirst (ar:Array Nat) (h: ar.size>0) : maxElement ar h ≥ ar.get ⟨0, h⟩ := by
  apply maxBiggerThanFirstOfList ar.data h

def maxBiggerThanIthOfList (as:List Nat) (h: as.length>0) (idx: Fin as.length) : maxOfList as h ≥ List.get as idx  := by
  induction as with
  | nil => {
    rw [List.length] at h
    exact False.elim ((Nat.not_lt_zero 0) h)
  }
  | cons a as' ih => {
    match idx with
    | ⟨0, _⟩ => {
      exact maxBiggerThanFirstOfList (a::as') (by {rw [List.length, Nat.add_one]; exact Nat.succ_pos _})
    }
    | ⟨Nat.succ b, ihh⟩ => {
      rw [List.get, maxOfList]
      simp
      unfold maxOfListAux
      simp
      cases as' with
      | nil => {
        simp
        apply False.elim
        simp at ihh
        apply Nat.not_succ_le_zero b
        apply Nat.le_of_lt_succ
        assumption
      }
      | cons a' as'' => {
        simp
        suffices q:List.length (a' :: as'') > 0 from (by {
          specialize ih q
          rw [maxOfList] at ih
          simp at ih
          have q2:b < Nat.succ (List.length as'') := by {
            simp at ihh
            apply Nat.lt_of_succ_lt_succ
            assumption
          }
          specialize ih ⟨b, q2⟩
          suffices neq: maxOfListAux (a' :: as'') ( by {rw [List.length, Nat.add_one]; exact Nat.succ_pos _}) a ≥ maxOfListAux (a' :: as'') ( by {simp [List.length]; rw [Nat.add_one]; apply Nat.succ_pos}) a' from (by {
            have good:= Nat.le_trans ih neq
            exact good
          })
          unfold maxOfListAux
          simp
          cases as'' with
          | nil => {
            simp
            by_cases h2: (a' > a)
            · simp [h2]
            · simp [h2]
              rw [Nat.not_gt_eq] at h2
              exact h2
          }
          | cons a'' as''' => {
            simp
            by_cases h2: (a' > a)
            · simp [h2]
            · simp [h2]
              rw [Nat.not_gt_eq] at h2
              exact maxOfListMoreCurrIsHigher (a''::as''') ( by {rw [List.length, Nat.add_one]; exact Nat.succ_pos _}) h2
          }
        })
        rw [List.length, Nat.add_one]
        exact Nat.succ_pos _
      }
    }
  }

def maxBiggerThanAll (ar:Array Nat) (h: ar.size>0) : ∀ idx:Fin ar.size, maxElement ar h ≥ ar.get idx := by
  intro idx
  rw [Array.get, maxElement]
  apply maxBiggerThanIthOfList (ar.data) h idx
