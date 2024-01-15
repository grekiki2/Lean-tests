import Graph.Graph
import Graph.Coloring
import Mathlib.Init.Function

-- K_n
def G_ex: Graph := K_n 4

instance (G: Graph) (k:Nat): DecidablePred (@valid_coloring G k) := by
  intro coloring
  exact Nat.decidableForallFin _

def is_k_colorable (G : Graph) (k: Nat) : Prop :=
  ∃ (coloring : Coloring G k), valid_coloring G coloring

instance {G : Graph} (k : Nat) : Decidable (is_k_colorable G k) := Fintype.decidableExistsFintype

def chromatic_number (G: Graph): ℕ :=
  @Nat.find (is_k_colorable G) _ (by {
    unfold is_k_colorable valid_coloring GraphConnected
    use G.vertexSize, λ i=>i
    intro a b hab
    by_contra h
    simp [← h] at hab
    exact (G.irreflexive a) hab
  })

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


theorem coloring_gives_ub (G: Graph) (k: Nat) (coloring : Coloring G k) : valid_coloring G coloring → chromatic_number G ≤ k := by
  intro h
  simp [chromatic_number, is_k_colorable]
  use k
  simp
  exact Exists.intro coloring h

lemma colorable_gives_ub (G: Graph) (k: Nat) : is_k_colorable G k ↔ chromatic_number G ≤ k := by
  constructor
  · intro h
    unfold is_k_colorable at h
    rcases h with ⟨coloring, h2⟩
    exact coloring_gives_ub G k coloring h2
  · intro h
    unfold chromatic_number at h
    simp at h
    rcases h with ⟨c, ⟨hc, h⟩⟩
    unfold is_k_colorable at *
    rcases h with ⟨coloring, h⟩
    exact extend_coloring G c k hc coloring h

theorem no_coloring_gives_lb (G: Graph) (k: Nat) : ¬is_k_colorable G k ↔ k < chromatic_number G := by
  constructor
  · intro h
    unfold chromatic_number
    simp
    unfold is_k_colorable at h ⊢
    intro m h2 ⟨coloring, h3⟩
    apply h
    exact extend_coloring G m k h2 coloring h3
  · intro h
    unfold chromatic_number at h
    simp at h
    specialize h k
    simp [h]

theorem bounds_give_chromatic (G:Graph) (k: Nat) : ¬is_k_colorable G k ∧ is_k_colorable G (k+1) ↔ chromatic_number G = k+1 := by
  constructor
  · rintro ⟨h1, h2⟩
    have lb := (no_coloring_gives_lb G k).mp h1
    unfold is_k_colorable at h2
    rcases h2 with ⟨coloring, h3⟩
    have ub := coloring_gives_ub G (k+1) coloring h3
    linarith
  · intro h
    constructor
    · have q:k<chromatic_number G := by linarith
      exact (no_coloring_gives_lb G k).mpr q
    · refine (colorable_gives_ub G (k + 1)).mpr ?mpr.right.a
      linarith

-- #eval chromatic_number (C_n 13 (by linarith))

theorem injective_le_chromatic (G G2:Graph) (f:Fin G2.vertexSize → Fin G.vertexSize) (f_inj:Function.Injective f) (f_inherits: ∀ a b, G2.connected a b → G.connected (f a) (f b)): chromatic_number G2 ≤ chromatic_number G := by
  apply (colorable_gives_ub _ _).mp
  have hG : is_k_colorable G (chromatic_number G) := by {
    apply (colorable_gives_ub G (chromatic_number G)).mpr
    simp
  }
  unfold is_k_colorable at hG
  rcases hG with ⟨coloringG, hG_valid⟩

  let coloringG2 : Fin G2.vertexSize → Fin (chromatic_number G) :=
    λ v => coloringG (f v)

  have hG2_valid : valid_coloring G2 coloringG2 := by {
    intro a b h_connected
    simp
    simp [GraphConnected] at h_connected
    specialize f_inherits a b h_connected
    unfold valid_coloring at hG_valid
    specialize hG_valid (f a) (f b)
    simp [GraphConnected] at hG_valid
    exact hG_valid f_inherits
  }

  unfold is_k_colorable
  use coloringG2
