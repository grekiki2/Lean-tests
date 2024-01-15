import Graph.Graph

@[reducible]
def Coloring (G:Graph) (k : Nat) := Fin G.vertexSize → Fin k

def valid_coloring (G:Graph) {k:Nat} (coloring: Coloring G k): Prop :=
  ∀ a b, GraphConnected G a b → coloring a ≠ coloring b
