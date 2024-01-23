import Mathlib

theorem succ_ne_mod (n:Nat): n%2 ≠ (n+1)%2 := by
  induction n with
  | zero => decide
  | succ n ih => {
    simp
    intro h
    apply ih
    rw [← Nat.add_one, Nat.add_assoc] at h
    simp at h
    exact id h.symm
  }

structure Tocka :=
    x: Nat
    y: Nat

def izhodisce : Tocka := {x := 0, y := 0}
