
def mx(a b:Nat) :=
  if a>b then a else b


theorem mx_symm (a b:Nat):mx a b = mx b a := by
  unfold mx
  by_cases hh:a=b
  · rw [hh]
  · by_cases h2: a>b
    · simp [h2]
      have q:b≤a := Nat.le_of_lt h2
      rw [← Nat.not_lt_eq] at q
      simp [q]
    · simp [h2]
      suffices h3:b>a by {
          simp [h3]
      }
      rw [Nat.not_lt_eq] at h2
      exact Nat.lt_of_le_of_ne h2 hh

@[simp]
theorem mx_aa (a:Nat): mx a a = a := by
  unfold mx
  simp
@[simp]
theorem mx_takes_bigger {a b:Nat}: a≥b → mx a b = a := by
  intro hh
  cases Nat.eq_or_lt_of_le hh with
  | inl h2 => rw [h2]; exact mx_aa _
  | inr h2 => unfold mx; simp [h2]
@[simp]
theorem mx_takes_gt {a b:Nat}: a>b → mx a b = a := by
  intro h
  exact mx_takes_bigger (Nat.le_of_lt h)

theorem mx_is_one (a b:Nat): mx a b = a ∨ mx a b = b := by
  by_cases h:a>b
  · simp [h]
  · rw [Nat.not_lt_eq] at h
    rw [mx_symm, mx_takes_bigger h]
    simp

theorem mx_bigger_than_fst (a b:Nat): mx a b ≥ a := by
  unfold mx
  by_cases h:a>b
  · simp [h]
  · simp [h]
    rw [Nat.not_lt_eq] at h
    assumption

theorem gt_increases_mx (a b c:Nat): a>b → mx a c ≥ mx b c := by
  intro h
  by_cases h2:b>c
  · simp [h, h2, Nat.lt_trans h2 h]
    exact Nat.le_of_lt h
  · rw [Nat.not_lt_eq] at h2
    rw [@mx_symm b c, mx_takes_bigger h2, mx_symm]
    exact mx_bigger_than_fst _ _

theorem ge_increases_mx (a b c:Nat): a≥b → mx a c ≥ mx b c := by
  intro h
  cases Nat.eq_or_lt_of_le h with
  | inl h2=> simp [h2]
  | inr h2=> exact gt_increases_mx _ _ _ h2
