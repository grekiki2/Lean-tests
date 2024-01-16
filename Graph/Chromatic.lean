import Graph.Graph
import Graph.Coloring
import Graph.Even
import Mathlib
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

theorem chromatic_number_of_C_n_even (n:Nat) (h:2*n≥2): chromatic_number (C_n (2*n) h) = 2 := by
  apply (bounds_give_chromatic _ _).mp
  constructor
  · unfold is_k_colorable
    intro ⟨coloring, valid_coloring⟩
    unfold valid_coloring at valid_coloring
    have size: (C_n (2*n) h).vertexSize=2*n := by simp [C_n]
    specialize valid_coloring ⟨0, by linarith⟩ ⟨1, by linarith⟩
    simp [GraphConnected, C_n] at valid_coloring
    apply valid_coloring
    have q2: ∀ x, coloring x = 0:= by {
      intro x
      exact Fin.eq_zero (coloring x)
    }
    simp [q2]
  · unfold is_k_colorable
    use λ i => ⟨i%2, by {
      refine Nat.mod_lt ↑i ?_
      trivial
    }⟩
    unfold valid_coloring
    intro a b
    simp [GraphConnected, C_n]
    intro hab
    unfold C_n at a b
    simp at a b
    -- Do tukaj je dokaz ok. Potem postane siten
    rcases hab with ((h' | h') | ⟨hl, hr⟩ )| ⟨hl, hr⟩
    · rw [h']
      exact (succ_ne_mod b).symm
    · rw [h']
      exact (succ_ne_mod a)
    · rw [hl]
      simp
      have q: (b+1)%2=(2*n)%2 := congrFun (congrArg HMod.hMod hr) 2
      simp at q
      have q2:= succ_ne_mod b
      intro h
      rw [← h, q] at q2
      trivial
    · rw [hl]
      simp
      have q: (a+1)%2=(2*n)%2 := congrFun (congrArg HMod.hMod hr) 2
      simp at q
      have q2:= succ_ne_mod a
      rw [q] at q2
      simp at q2
      trivial

#check Fin.ext_iff
#check congrArg
theorem chromatic_number_of_C_n_odd (n:Nat) (h:2*n+1≥2): chromatic_number (C_n (2*n+1) h) = 3 := by
  apply (bounds_give_chromatic _ _).mp
  constructor
  · unfold is_k_colorable
    intro ⟨col, valid_col⟩
    simp [Coloring, C_n] at col
    unfold valid_coloring GraphConnected at valid_col
    simp [C_n] at valid_col
    have color_prop:∀ idx: Nat, idx<2*n+1 → (idx%2=1 → col idx ≠ col 0) ∧ (idx%2=0 → col idx = col 0) := by {
      -- intro idx
      -- induction idx with
      -- | zero => simp
      -- | succ idxl ih => {
      --   intro h
      --   have q:idxl<2*n+1 := by linarith
      --   specialize ih q
      --   simp at ih ⊢
      --   match mod:idxl%2 with
      --   | 0 => {
      --     simp [mod] at ih
      --     have mod_succ:Nat.succ idxl % 2 = 1:= by {
      --       rw [←Nat.add_one]
      --       have q3:= succ_ne_mod idxl
      --       rw [mod] at q3
      --       simp at q3
      --       exact Nat.succ_mod_two_eq_one_iff.mpr mod
      --     }
      --     simp [mod_succ]
      --     rw [← ih]
      --     specialize valid_col ⟨↑idxl+1, by linarith⟩ ⟨↑idxl, by linarith⟩
      --     simp at valid_col
      --     intro hh
      --     apply valid_col
      --     have q3:col { val := idxl + 1, isLt := by linarith } = col (↑idxl+1) := by {
      --       congr
      --       rw [← Nat.add_one] at h
      --       simp [h]
      --       exact (Nat.mod_eq_of_lt h).symm
      --     }
      --     rw [q3]
      --     have q4:col { val := idxl, isLt := by linarith } = col (↑idxl) := by {
      --       congr
      --       exact (Nat.mod_eq_of_lt q).symm
      --     }
      --     rw [q4]
      --     assumption
      --   }
      --   | 1 => {
      --     simp [mod] at ih
      --     have mod_succ:Nat.succ idxl % 2 = 0:= by {
      --       rw [←Nat.add_one]
      --       have q3:= succ_ne_mod idxl
      --       rw [mod] at q3
      --       simp at q3
      --       exact Nat.succ_mod_two_eq_zero_iff.mpr mod
      --     }
      --     simp [mod_succ]
      --     specialize valid_col ⟨↑idxl+1, by linarith⟩ ⟨↑idxl, by linarith⟩
      --     simp at valid_col
      --     clear mod_succ mod
      --     have q3:col { val := idxl + 1, isLt := by linarith } = col (↑idxl+1) := by {
      --       congr
      --       rw [← Nat.add_one] at h
      --       simp [h]
      --       exact (Nat.mod_eq_of_lt h).symm
      --     }
      --     have q4:col { val := idxl, isLt := by linarith } = col (↑idxl) := by {
      --       congr
      --       exact (Nat.mod_eq_of_lt q).symm
      --     }
      --     rw [q3, q4] at valid_col
      --     match h:col ⟨0, by linarith⟩ with
      --     | ⟨0, _⟩ => {
      --       simp at h
      --       rw [h] at ih
      --       simp
      --       match h2:col ⟨idxl, by linarith⟩ with
      --       | ⟨0, _⟩ => {
      --         simp at h2
      --         rw [q4] at h2
      --         exfalso
      --         exact ih h2
      --       }
      --       | ⟨1, _⟩ => {
      --         simp at h2
      --         rw [q4] at h2
      --         rw [h2] at valid_col
      --         match h3:col ⟨idxl+1, by linarith⟩ with
      --         | ⟨0, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           assumption
      --         }
      --         | ⟨1, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           exfalso
      --           exact valid_col h3
      --         }
      --       }
      --     }
      --     | ⟨1, _⟩ => {
      --       simp at h ⊢
      --       rw [h] at ih
      --       match h2:col ⟨idxl, by linarith⟩ with
      --       | ⟨0, _⟩ => {
      --         simp at h2
      --         rw [q4] at h2
      --         rw [h2] at valid_col
      --         match h3:col ⟨idxl+1, by linarith⟩ with
      --         | ⟨0, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           exfalso
      --           exact valid_col h3
      --         }
      --         | ⟨1, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           assumption
      --         }
      --       }
      --       | ⟨1, _⟩ => {
      --         simp at h2
      --         rw [q4] at h2
      --         rw [h2] at valid_col
      --         match h3:col ⟨idxl+1, by linarith⟩ with
      --         | ⟨0, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           rw [h3]
      --           trivial
      --         }
      --         | ⟨1, _⟩ => {
      --           simp at h3
      --           rw [q3] at h3
      --           assumption
      --         }
      --       }
      --     }
      --   }
      --   | n+2 => { --Impossible
      --     exfalso
      --     rw [← Nat.add_one, Nat.add_assoc] at mod
      --     have q2:= @Nat.mod_lt idxl 2 (by linarith)
      --     rw [mod] at q2
      --     linarith
      --   }
      -- }
      sorry
    }
    specialize color_prop (2*n) (by linarith)
    simp at color_prop
    specialize valid_col ⟨0, by linarith⟩ ⟨2*n, by linarith⟩
    simp at valid_col
    apply valid_col
    rw [← color_prop]
    apply congrArg
    sorry
  · unfold is_k_colorable
    use λ i => (if i.val=0 then 2 else ⟨i%2, by {
      refine Nat.lt_add_right 1 ?_
      refine Nat.mod_lt ↑i ?_
      trivial
    }⟩)
    unfold valid_coloring C_n GraphConnected
    simp
    intro a b hab
    by_cases aeq0: a.val=0
    · simp [aeq0]
      rcases hab with ((h' | h') | ⟨hl, hr⟩ )| ⟨hl, hr⟩
      · exfalso
        rw [aeq0, Nat.add_one] at h'
        exact Nat.succ_ne_zero (↑b) h'.symm
      · simp [aeq0] at h'
        simp [h']
        trivial
      · have q:b.val≠0 := by linarith
        simp [q]
        intro h
        have q2:(2:Nat)=↑b % 2 := by {
          have q3:= Fin.ext_iff.mp h
          rw [hr] at q3
          simp at q3
        }
        have q4:=@Nat.mod_lt b 2
        simp at q4
        linarith
      · simp [hl]
        linarith
    · simp [aeq0]
      by_cases beq0: b.val=0
      · simp [beq0]
        intro h
        have q4:=@Nat.mod_lt a 2
        simp at q4
        have q3:= Fin.ext_iff.mp h
        simp at q3
        linarith
      · simp [aeq0, beq0]
        rcases hab with ((h' | h') | ⟨hl, hr⟩ )| ⟨hl, hr⟩
        · rw [h']
          exact (succ_ne_mod b).symm
        · rw [h']
          exact (succ_ne_mod a)
        · rw [hl, hr]
          simp
          exact aeq0 hl
        · exfalso
          exact beq0 hl
