import Lake
open Lake DSL

require GameServer from "../lean4game/server"
require mathlib from "../mathlib4"

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩]

@[default_target]
lean_lib Game
