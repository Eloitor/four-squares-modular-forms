import Lake
open Lake DSL

package «FourSquaresModularForms» where
  -- srcDir relative module layout, see `lean_lib` below

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.32.2"

@[default_target]
lean_lib FourSquaresModularForms where
  srcDir := "src"
