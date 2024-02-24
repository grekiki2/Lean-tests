import Graph
def k_colorable_test (p:Nat) (g:StdGen) (n:Nat) (colors:Nat) : Bool := Id.run do
  let mut edges : Array (Array (Fin n)) := {}
  for _ in [0:n] do
    edges := edges.push (List.toArray [])
  let mut a:= randNat g 0 100
  for i in [0:n] do
    for j in [0:n] do
      if i < j then
        a := randNat a.snd 0 100
        if h:a.fst < p ∧ i<n ∧ j<n then
          edges := edges.set! i ((edges.get! i).push ⟨j, by linarith⟩)
          edges := edges.set! j ((edges.get! j).push ⟨i, by linarith⟩)

  if h: edges.size = n then
    let mut g1 : Graph := {
      vertexSize := n
      , connected := λ x y => x≠y ∧ (y ∈ edges[x]'(by rw [h]; exact Fin.prop x) ∨ x ∈ edges[y]'(by rw [h]; exact Fin.prop y))
      , connected_decidable := by {
        intro x y
        simp
        apply And.decidable
      }
      , irreflexive := by {
        intro a
        simp
      }
      , symmetric := by {
        intro a b
        simp
        intro h h2
        constructor
        · exact Ne.symm h
        · exact Or.symm h2
      }
    }

    if Is2ColorableFast g1 then
      true
    else
      false
    -- if is_k_colorable g1 colors then
    --   true
    -- else
    --   false
  else
    false


def main (args : List String) : IO Unit := do
  -- IO.println "Starting"
  let mut gen:StdGen := { s1 := 0, s2 := 1 }

  let n := args[0]!.toNat!
  let p_connected := args[1]!.toNat!
  let colors := args[2]!.toNat!

  let mut success := 0
  for _ in [0:1000] do
    gen := (stdNext gen).snd
    if k_colorable_test p_connected gen n colors then
      success := success + 1
  IO.println s!"{success/10}\n % of graphs on {n} vertices p={p_connected}% are {colors}-colorable"
  IO.println "done"
