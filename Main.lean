import Graph

def main : IO Unit := do

  let G := C_n 11 (by {linarith})
  let num := chromatic_number G
  IO.println s!"chromatic number = {num}"
  -- IO.println "Done!"
