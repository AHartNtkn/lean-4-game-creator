import Game.Levels.CosetBasics.L01_LeftCosets
import Game.Levels.CosetBasics.L02_SelfMembership
import Game.Levels.CosetBasics.L03_CosetEqIff
import Game.Levels.CosetBasics.L04_EqToMem
import Game.Levels.CosetBasics.L05_MemToEq
import Game.Levels.CosetBasics.L06_Reflexivity
import Game.Levels.CosetBasics.L07_Symmetry
import Game.Levels.CosetBasics.L08_Transitivity
import Game.Levels.CosetBasics.L09_Boss

World "CosetBasics"
Title "Cosets"
Introduction
"
Subgroups partition a group into pieces of equal size called **cosets**.

If `H` is a subgroup of `G` and `a ∈ G`, the **left coset** `aH` is
`{a * h | h ∈ H}`. In Lean this is written `a • (H : Set G)`.

Two cosets `aH` and `bH` are either identical or disjoint — never
partially overlapping. The condition for equality is:

`aH = bH ↔ a⁻¹ * b ∈ H`

This world develops the two key unfolding lemmas (`mem_leftCoset_iff`
and `leftCoset_eq_iff`), then uses them to prove that the relation
`a⁻¹ * b ∈ H` is an equivalence relation — the foundation for
quotient groups.
"
