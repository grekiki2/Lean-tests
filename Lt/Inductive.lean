namespace Hidden
inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α

inductive Option2 (α : Type u) where
  | none
  | some (a : α)

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α

open Nat

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n
  case zero => rfl
  case succ n ih => rw [add_succ, ih]

end Hidden

namespace Hidden
inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List

def append (as bs : List α) : List α :=
  match as with
  | nil       => bs
  | cons a as => cons a (append as bs)

theorem nil_append (as : List α) : append nil as = as :=
  rfl

theorem cons_append (a : α) (as bs : List α)
                    : append (cons a as) bs = cons a (append as bs) :=
  rfl

theorem append_nil (as : List α) : append as nil = as := by
  induction as
  case nil => rfl
  case cons a as ih => rw [append, ih]

theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) := by
  induction as
  case nil => rw [append, append]
  case cons a as ih => rw [append, append, append, ih]

def len (as: List α) :=
  match as with
  | nil => 0
  | cons _ as' => 1+(len as')

theorem len_additive (as bs: List α) : (len as) + (len bs) = len (append as bs) := by
  induction as
  case nil => rw [nil_append, len, Nat.zero_add]
  case cons b bs' ih => rw [len, append, len, Nat.add_assoc, ih]

end List
end Hidden
