import Lake
open Lake DSL

package alg

lean_lib Lt
lean_lib Gt
lean_lib Graph

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe dump where
  root := `Main
