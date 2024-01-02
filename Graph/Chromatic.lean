import Graph.Graph
import Lt.Sorted


#check Fintype
#check Fintype.card

#check Finset

-- K_n graph
def G_ex: Graph := {vertexSize:=7, connected:=(λ x y=>x ≠ y), connected_decidable := by {simp; intro a b;apply Not.decidable}, irreflexive := by simp, symmetric:= by {apply Ne.symm} }

@[reducible]
def Coloring (G:Graph) (k : Nat) := Fin G.vertexSize → Fin k

#eval Fintype.card (Coloring G_ex 3)

def Valid_coloring (G:Graph) {k:Nat} (coloring: Coloring G k): Prop :=
  ∀ a b, GraphConnected G a b → coloring a ≠ coloring b

instance (G : Graph) (k:Nat): DecidablePred (@Valid_coloring G k) := by
  intro coloring
  exact Nat.decidableForallFin _

def is_k_colorable (G : Graph) (k : Nat) : Prop :=
  ∃ (coloring : Coloring G k), Valid_coloring G coloring

instance {G : Graph} (k : Nat) : Decidable (is_k_colorable G k) := Fintype.decidableExistsFintype

#eval is_k_colorable G_ex 4

def chromatic_number (G : Graph): ℕ :=
  @Nat.find (is_k_colorable G) _ (by {
    unfold is_k_colorable Valid_coloring GraphConnected
    use G.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    exact (G.irreflexive a) hab
  })

#eval chromatic_number G_ex
