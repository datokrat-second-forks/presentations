import Lake
open Lake DSL

require «verso-slides» from git
  "https://github.com/leanprover/verso-slides.git" @ "main"
require mathlib from "../../mathlib4/julia-minimal"

package «instance-assignment-failures» where
  version := v!"0.1.0"

@[default_target]
lean_lib Deck where
  needs := #[`@verso/+Verso.Code.External:highlighted]

lean_exe «slides» where
  root := `Main
