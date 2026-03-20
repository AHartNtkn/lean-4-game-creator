import Lake
open Lake DSL

require GameServer from "../lean4game/server"
require "leanprover-community" / mathlib @ git "v4.29.0-rc6"

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩]

@[default_target]
lean_lib Game
