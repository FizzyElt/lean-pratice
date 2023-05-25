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
  @"7e05f55c01e9f79dbbbec7758e1b93716a988536"