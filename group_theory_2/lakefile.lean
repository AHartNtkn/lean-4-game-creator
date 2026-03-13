import Lake
open Lake DSL

require GameServer from "../lean4game/server"

package Game where
  leanOptions := #[
    ⟨`linter.all, false⟩]

@[default_target]
lean_lib Game
