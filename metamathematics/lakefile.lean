import Lake
open Lake DSL

require GameServer from "../lean4game/server"
require "leanprover-community" / mathlib @ git "v4.28.0"

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩]

@[default_target]
lean_lib Game
