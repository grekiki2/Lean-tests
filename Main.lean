import Graph

def main : IO Unit := do

  for n in [1:8] do
    let G := K_n n
    let num := chromatic_number G
    IO.println s!"n = {n}, chromatic number = {num}"
  IO.println "Done!"
