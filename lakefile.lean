import Lake
open Lake DSL

package «algebra» {
  -- add package configuration options here
}

lean_lib «Algebra» {
  -- add library configuration options here
}

@[default_target]
lean_exe «algebra» {
  root := `Main
}


require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
  @"5a919533f110b7d76410134a237ee374f24eaaad"
require std from git
  "https://github.com/leanprover/std4.git"@"d5471b83378e8ace4845f9a029af92f8b0cf10cb"