import Graph.Chromatic
import Graph.Graph
import Mathlib

def is_2_colorable (G :Graph) :Bool := is_k_colorable G 2


-- #eval is_2_colorable (C_n 4 (by linarith))
-- #eval is_2_colorable (C_n 5 (by linarith))

-- #check chromatic_number_of_C_n_odd 1

def find_2coloring (G:Graph) : Sum Unit (Sum (Array (Fin 2)) (List (Fin G.vertexSize))) := Id.run <| do
  let mut coloring: Array (Option (Fin 2)) := Array.mkArray G.vertexSize none
  let mut par: Array (Option (Fin G.vertexSize)) := Array.mkArray G.vertexSize none
  for i in [0:G.vertexSize] do
    if h:i<G.vertexSize then
      if coloring[i]!.isNone then
        let root:Fin G.vertexSize := ⟨i, h⟩
        let mut bfs : List (Fin G.vertexSize) := [⟨i, by linarith⟩]
        coloring := coloring.set! i (some 0)
        while h:bfs.length > 0 do
          let v := bfs.head (List.length_pos.mp h)
          bfs := bfs.tail
          let color := coloring[v]!
          match color with
          | none => return Sum.inl ()
          | some color' => {
            for j in [0:G.vertexSize] do
              if h2:j<G.vertexSize then
                if GraphConnected G v ⟨j, by linarith⟩ then
                  if coloring[j]!.isNone then
                    coloring := coloring.set! j (some ⟨1-color', by {
                      match color' with
                      | 0 => simp
                      | 1 => simp
                    }⟩)
                    par := par.set! j (some v)
                    bfs := ⟨j, h2⟩ :: bfs
                  else if coloring[j]! == color then
                    -- Imamo protislovje. Izgradimo poti j-root in v-root
                    let mut path1 : List (Fin G.vertexSize) := [⟨j, by linarith⟩]
                    let mut vert := ⟨j, by linarith⟩
                    while vert≠root do
                      let par2 := (par[vert]!)
                      match par2 with
                      | none => return Sum.inl ()
                      | some par2' =>
                        path1 := par2' :: path1
                        vert := par2'
                    let mut path2 : List (Fin G.vertexSize) := [v]
                    vert := v
                    while vert≠root do
                      let par2 := (par[vert]!)
                      match par2 with
                      | none => return Sum.inl ()
                      | some par2' =>
                        path2 := par2' :: path2
                        vert := par2'
                    dbg_trace path1
                    dbg_trace path2
                    return Sum.inr (Sum.inr (path1 ++ (List.reverse path2.tail)))
          }
  let mut coloringAns : Array (Fin 2) := Array.mkArray G.vertexSize 0
  for i in [0:G.vertexSize] do
    if coloring[i]!.isSome then
      match coloring[i]! with
      | none => return Sum.inl ()
      | some color => coloringAns := coloringAns.set! i color
  return Sum.inr (Sum.inl coloringAns)

-- #eval find_2coloring (C_n 1000 (by linarith))

def is_2_colorable_fast (G : Graph):Bool :=
  match find_2coloring G with
  | Sum.inl _ => is_k_colorable G 2
  | Sum.inr (Sum.inl coloring) =>
    if h:coloring.size = G.vertexSize then
      if valid_coloring G (λ idx => coloring[idx]'(by {rw [h];exact Fin.prop idx})) then true else is_k_colorable G 2
      else is_k_colorable G 2
  | Sum.inr (Sum.inr cycle) =>
    if h:cycle.length < 3 then is_k_colorable G 2 else
      let G_sub := C_n cycle.length (by linarith)
      if (∀ a b, G_sub.connected a b → G.connected cycle[a] cycle[b]) ∧ cycle.length%2=1 -- we need this for subgraph proof
      then false --not 2 colorable
      else is_k_colorable G 2

#check Nat.mod
#check Nat.div_add_mod
#check Nat.sub
lemma mod_exists_0 (n:Nat) (h:n%2=0): ∃ k,n=2*k := by {
  use n/2
  match n with
  | 0 => simp;
  | n'+1 =>
    have q:=
      calc 2*((n'+1)/2)
      _ = 2*((n'+1)/2)+(n'+1)%2-(n'+1)%2 := by simp
      _ = (n'+1)-(n'+1)%2 := by rw [Nat.div_add_mod]
      _ = n'+1 := by {rw [h]; simp}
    exact q.symm
}
lemma mod_exists (n:Nat) (h:n%2=1): ∃ k,n=2*k+1 := by {
  use n/2
  -- rw [Nat.div_add_mod 2 n]
  match n with
  | 0 => simp at h;
  | n'+1 =>
    have q:=
      calc 2*((n'+1)/2)+1
      _ = 2*((n'+1)/2)+(n'+1)%2-(n'+1)%2+1 := by simp
      _ = (n'+1)-(n'+1)%2+1 := by rw [Nat.div_add_mod]
      _ = n'+1 := by {rw [h]; simp}
    exact q.symm
}
theorem chromatic_number_of_C_n (n:Nat) (h:n≥2): chromatic_number (C_n n h) = 2+(n%2) := by
  match mod:n%2 with
  | 0 =>
    have ⟨num, h2⟩ := mod_exists_0 n (by linarith)
    have q:= (chromatic_number_of_C_n_even num (by linarith)).symm
    have q2: 2+0=2 := by simp
    rw [q2, q]
    simp [h2]
  | 1 =>
    have ⟨num, h2⟩ := mod_exists n (by linarith)
    have q:= (chromatic_number_of_C_n_odd num (by linarith)).symm
    have q2: 2+1=3 := by simp
    rw [q2, q]
    simp [h2]
  | n'+2 =>
    exfalso
    rw [← Nat.add_one, Nat.add_assoc] at mod
    have q2:= @Nat.mod_lt n 2 (by linarith)
    rw [mod] at q2
    linarith

theorem is_2_colorable_fast_correct : is_2_colorable_fast = is_2_colorable := by
  funext G
  unfold is_2_colorable is_2_colorable_fast
  match h:find_2coloring G with
  | Sum.inl _ => simp
  | Sum.inr (Sum.inl coloring) =>
    simp
    intro h2 h3
    unfold is_k_colorable
    use λidx => coloring[idx]'(by {rw [h2];exact Fin.prop idx}); assumption
  | Sum.inr (Sum.inr cycle) =>
    simp
    intro len h2 h3
    have q:= sub_le_chromatic G (C_n cycle.length (by linarith)) (λ idx => cycle[idx]) h2
    suffices ch3:chromatic_number (C_n (List.length cycle) (by linarith)) = 3 from by {
      rw [ch3] at q
      apply (no_coloring_gives_lb G 2).mpr
      exact q
    }
    rw [chromatic_number_of_C_n]
    simp [h3]


#eval is_2_colorable_fast (K_n 1000)
#eval is_2_colorable_fast (C_n 1000 (by linarith))
#eval is_2_colorable_fast (C_n 1001 (by linarith))
