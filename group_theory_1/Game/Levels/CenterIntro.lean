import Game.Levels.CenterIntro.L01_CenterMem
import Game.Levels.CenterIntro.L02_CenterOne
import Game.Levels.CenterIntro.L03_CenterMul
import Game.Levels.CenterIntro.L04_CenterInv
import Game.Levels.CenterIntro.L05_CenterEqTop
import Game.Levels.CenterIntro.L06_TopMeansAbelian
import Game.Levels.CenterIntro.L07_Boss

World "CenterIntro"
Title "The Center"
Introduction
"
In the previous worlds, you proved that the *centralizer* of an element
`a` — the set `{g | a * g = g * a}` — is a subgroup. But what if we
demand more: what if an element commutes with *everything* in `G`?

The **center** of a group `G`, written `Z(G)` in mathematics and
`Subgroup.center G` in Lean, is exactly this:

`center G = {z : G | ∀ g : G, g * z = z * g}`

Every element of the center commutes with every element of the group.
The center is always a subgroup — you'll prove its three closure
properties in this world.

The center measures how close a group is to being abelian:
- If `Z(G) = G` (the center is everything), then every pair commutes
  and `G` is abelian.
- If `Z(G) = {1}` (only the identity is central), the group is
  \"as non-abelian as possible.\"

The gateway lemma is `Subgroup.mem_center_iff`:

`z ∈ center G ↔ ∀ g, g * z = z * g`

Every proof in this world starts by converting center membership
to this universal commuting condition.
"
