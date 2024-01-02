import Graph.Graph
import Graph.Coloring
import Lt.Sorted

-- K_n
def G_ex: Graph := {vertexSize:=7, connected:=(λ x y=>x ≠ y), connected_decidable := by simp; intro a b;apply Not.decidable, irreflexive := by simp, symmetric:= by apply Ne.symm }

#eval Fintype.card (Coloring G_ex 3)

instance (G : Graph) (k:Nat): DecidablePred (@valid_coloring G k) := by
  intro coloring
  exact Nat.decidableForallFin _

def is_k_colorable (G : Graph) (k : Nat) : Prop :=
  ∃ (coloring : Coloring G k), valid_coloring G coloring

instance {G : Graph} (k : Nat) : Decidable (is_k_colorable G k) := Fintype.decidableExistsFintype

#eval is_k_colorable G_ex 4

def chromatic_number (G : Graph): ℕ :=
  @Nat.find (is_k_colorable G) _ (by {
    unfold is_k_colorable valid_coloring GraphConnected
    use G.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    exact (G.irreflexive a) hab
  })

#eval chromatic_number G_ex
