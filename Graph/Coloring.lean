import Graph.Graph

@[reducible]
def Coloring (G:Graph) (k : Nat) := Fin G.vertexSize → Fin k

@[reducible]
def Coloring2 (G2:Graph2) (k : Nat) := Fin G2.vertexSize → Fin k

def valid_coloring (G:Graph) {k:Nat} (coloring: Coloring G k): Prop :=
  ∀ a b, GraphConnected G a b → coloring a ≠ coloring b

def valid_coloring2 (G2:Graph2) {k:Nat} (coloring: Coloring2 G2 k): Prop :=
  ∀ i j:Fin G2.vertexSize, Graph2Connected G2 i j → coloring i ≠ coloring j

theorem colorings_convert (G: Graph) (coloring: Coloring G k): valid_coloring G coloring ↔ valid_coloring2 (convertGraphToGraph2 G) coloring := by
  constructor
  · intro h
    unfold valid_coloring at h
    unfold valid_coloring2
    intro i j cij
    rw [← connected_iff] at cij
    exact h i j cij
  · intro h
    unfold valid_coloring2 at h
    unfold valid_coloring
    intro i j cij
    rw [connected_iff] at cij
    exact h i j cij
