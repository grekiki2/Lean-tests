import Graph.Graph
import Graph.Coloring
import Lt.Sorted

-- K_n
def G_ex: Graph := {vertexSize:=7, connected:=(λ x y=>x ≠ y), connected_decidable := by simp; intro a b;apply Not.decidable, irreflexive := by simp, symmetric:= by apply Ne.symm }
def G_ex_2 := convertGraphToGraph2 G_ex
#eval Fintype.card (Coloring G_ex 3)
#eval Fintype.card (Coloring2 G_ex_2 3)

instance (G: Graph) (k:Nat): DecidablePred (@valid_coloring G k) := by
  intro coloring
  exact Nat.decidableForallFin _

instance (G2: Graph2) (k:Nat): DecidablePred (@valid_coloring2 G2 k) := by
  intro coloring
  exact Nat.decidableForallFin _

def is_k_colorable (G : Graph) (k: Nat) : Prop :=
  ∃ (coloring : Coloring G k), valid_coloring G coloring

instance {G : Graph} (k : Nat) : Decidable (is_k_colorable G k) := Fintype.decidableExistsFintype

def is_k_colorable2 (G2: Graph2) (k: Nat) : Prop :=
  ∃ (coloring2 : Coloring2 G2 k), valid_coloring2 G2 coloring2

instance {G2 : Graph2} (k : Nat) : Decidable (is_k_colorable2 G2 k) := Fintype.decidableExistsFintype

theorem is_k_colorable_eq (G: Graph) (k: Nat) : is_k_colorable G k = is_k_colorable2 (convertGraphToGraph2 G) k := by
  unfold is_k_colorable is_k_colorable2
  apply Iff.to_eq
  constructor
  · rintro ⟨coloring, h⟩
    use coloring
    exact (colorings_convert G coloring).mp h
  · rintro ⟨coloring2, h⟩
    use coloring2
    exact (colorings_convert G coloring2).mpr h
theorem is_k_colorable_eq2 (G: Graph) : is_k_colorable G = is_k_colorable2 (convertGraphToGraph2 G) := by
  ext k
  unfold is_k_colorable is_k_colorable2
  constructor
  · rintro ⟨coloring, h⟩
    use coloring
    exact (colorings_convert G coloring).mp h
  · rintro ⟨coloring2, h⟩
    use coloring2
    exact (colorings_convert G coloring2).mpr h
-- #eval is_k_colorable G_ex 10
-- #eval is_k_colorable2 G_ex_2 10

def chromatic_number (G: Graph): ℕ :=
  @Nat.find (is_k_colorable G) _ (by {
    unfold is_k_colorable valid_coloring GraphConnected
    use G.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    exact (G.irreflexive a) hab
  })

def chromatic_number2 (G2: Graph2) : ℕ :=
  @Nat.find (is_k_colorable2 G2) _ (by {
    unfold is_k_colorable2 valid_coloring2 Graph2Connected
    use G2.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    have q:= G2.edgeIrreflexive a
    simp at q
    apply q
    exact Array.contains_def.mp hab
  })

theorem chromatic_colorable (G2: Graph2): is_k_colorable2 G2 (chromatic_number2 G2) := by
  unfold chromatic_number2
  -- Maybe refactor this?
  exact @Nat.find_spec (is_k_colorable2 G2) _ (by {
    unfold is_k_colorable2 valid_coloring2 Graph2Connected
    use G2.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    have q:= G2.edgeIrreflexive a
    simp at q
    apply q
    exact Array.contains_def.mp hab
  })

theorem chromatic_number_eq (G: Graph) : chromatic_number G = chromatic_number2 (convertGraphToGraph2 G) := by
  unfold chromatic_number
  have q:= @Nat.find_eq_iff (chromatic_number2 (convertGraphToGraph2 G)) (is_k_colorable G) _ (by {
    unfold is_k_colorable valid_coloring GraphConnected
    use G.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    exact (G.irreflexive a) hab
  })
  simp [q]
  clear q
  constructor
  · rw [is_k_colorable_eq2]
    exact chromatic_colorable (convertGraphToGraph2 G)
  · intro n hn h2
    rw [is_k_colorable_eq2] at h2
    unfold chromatic_number2 at hn
    have q:= Nat.find_min (Exists.intro n h2) hn
    exact q h2

-- #eval chromatic_number G_ex
-- #eval chromatic_number2 G_ex_2

theorem coloring_gives_ub (G: Graph) (k: Nat) (coloring : Coloring G k) : valid_coloring G coloring → chromatic_number G ≤ k := by
  intro h
  simp [chromatic_number, is_k_colorable]
  use k
  simp
  exact Exists.intro coloring h

def extend_coloring (G:Graph) (k1 k2: Nat) (h:k2≥k1) (coloring: Coloring G k1) (h2: valid_coloring G coloring):∃ coloring2:Coloring G k2, valid_coloring G coloring2 := by
  unfold Coloring at *
  use λ i =>⟨coloring i, Fin.val_lt_of_le (coloring i) h⟩
  unfold valid_coloring at *
  intro a b
  specialize h2 a b
  intro gcab
  specialize h2 gcab
  simp
  exact Fin.vne_of_ne h2

theorem no_coloring_gives_lb (G: Graph) (k: Nat) : ¬is_k_colorable G k → k < chromatic_number G := by
  intro h
  unfold chromatic_number
  simp
  unfold is_k_colorable at h ⊢
  intro m h2 ⟨coloring, h3⟩
  apply h
  exact extend_coloring G m k h2 coloring h3

theorem bounds_give_chromatic (G:Graph) (k: Nat) : ¬ is_k_colorable G k → is_k_colorable G (k+1) → chromatic_number G = k+1 := by
  intro h1 h2
  have lb := no_coloring_gives_lb G k h1
  unfold is_k_colorable at h2
  rcases h2 with ⟨coloring, h3⟩
  have ub := coloring_gives_ub G (k+1) coloring h3
  linarith
