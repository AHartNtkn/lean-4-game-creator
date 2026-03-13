import Game.Levels.SubgroupPset.L01_InfLELeft
import Game.Levels.SubgroupPset.L02_InfPreservesLE
import Game.Levels.SubgroupPset.L03_LETransitive
import Game.Levels.SubgroupPset.L04_BotInfEqBot
import Game.Levels.SubgroupPset.L05_InverseCarrier
import Game.Levels.SubgroupPset.L06_LEAntisymm
import Game.Levels.SubgroupPset.L07_Boss

World "SubgroupPset"
Title "Subgroup Problem Set"

Introduction
"
Welcome to the **Subgroup Problem Set** — practice under reduced
scaffolding.

You have all the tools from the last two worlds: membership lemmas
(`one_mem`, `mul_mem`, `inv_mem`), lattice operations (`≤`, `⊥`, `⊤`,
`⊓`), and the structural tactics (`obtain`, `ext`, `refine`, `show`).
No new tactics or theorems here — just fresh problems that exercise
the same proof moves on different surfaces.

The boss: prove that `H ⊓ K = H` if and only if `H ≤ K` — connecting
intersection and containment.
"
