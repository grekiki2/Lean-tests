import Lake
open Lake DSL

package alg

lean_lib Lt
lean_lib Gt

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe dump where
  root := `Main
