import Lake
open Lake DSL

package alg

lean_lib Lt
lean_lib Gt

@[default_target]
lean_exe dump where
  root := `Main
