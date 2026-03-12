import Game.Levels.SubgroupDef.L01_SubgroupMembership
import Game.Levels.SubgroupDef.L02_MulMem
import Game.Levels.SubgroupDef.L03_InvMem
import Game.Levels.SubgroupDef.L04_CombiningMembership
import Game.Levels.SubgroupDef.L05_ShowTactic
import Game.Levels.SubgroupDef.L06_IntroTactic
import Game.Levels.SubgroupDef.L07_BuildingTrivial
import Game.Levels.SubgroupDef.L08_CentralizerMulMem
import Game.Levels.SubgroupDef.L09_CentralizerInvMem
import Game.Levels.SubgroupDef.L10_WholeGroupSubgroup
import Game.Levels.SubgroupDef.L11_Boss

World "SubgroupDef"
Title "Subgroup Definitions"

Introduction
"
Welcome to **Subgroup Definitions**, where you'll learn what it means
for a subset of a group to form a group in its own right.

A **subgroup** `H` of a group `G` is a subset that is closed under
the group operations:

1. The identity `1` belongs to `H`
2. If `x` and `y` belong to `H`, then `x * y` belongs to `H`
3. If `x` belongs to `H`, then `x⁻¹` belongs to `H`

Why do we need all three? Consider the positive integers under addition:
they are closed under addition (the sum of two positive integers is
positive), but they don't contain the identity `0` and they don't
contain additive inverses (negatives). So being closed under the
operation alone is not enough to be a subgroup — you also need the
identity and inverses.

In Lean, this is captured by the type `Subgroup G`. If `H : Subgroup G`
and `x : G`, we write `x ∈ H` for membership.

The first half of this world teaches you to *use* subgroups — applying
the membership lemmas `one_mem`, `mul_mem`, and `inv_mem`. The second
half teaches you to *build* them — constructing a `Subgroup G` from
a carrier set and proving the three closure properties.

By the boss level, you'll prove that the **centralizer** of an element
`a` — the set `{g : G | a * g = g * a}` of all elements commuting
with `a` — is a subgroup. This requires all three closure proofs,
each of which is a real piece of group algebra.
"
