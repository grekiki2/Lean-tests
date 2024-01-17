import Graph.Chromatic
import Graph.Graph
-- import Mathlib

def is_2_colorable (G :Graph) :Bool := is_k_colorable G 2


-- #eval is_2_colorable (C_n 4 (by linarith))
-- #eval is_2_colorable (C_n 5 (by linarith))

-- #check chromatic_number_of_C_n_odd 1

def find_2coloring (G:Graph) : Sum Unit (Sum (Array (Option (Fin 2))) (List (Fin G.vertexSize))) := Id.run <| do
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
                    -- dbg_trace path1
                    -- dbg_trace path2
                    return Sum.inr (Sum.inr (path1 ++ path2.tail))
          }
  return Sum.inr (Sum.inl coloring)

#eval find_2coloring (C_n 5 (by linarith))


def is_2_colorable_fast (G : Graph):Bool :=
  sorry
