import Game.Levels.NormalDef.L01_NormalDef
import Game.Levels.NormalDef.L02_TopNormal
import Game.Levels.NormalDef.L03_HaveTactic
import Game.Levels.NormalDef.L04_MemComm
import Game.Levels.NormalDef.L05_CosetNormality
import Game.Levels.NormalDef.L06_KernelConjugation
import Game.Levels.NormalDef.L07_BotNormal
import Game.Levels.NormalDef.L08_KernelProductConj
import Game.Levels.NormalDef.L09_Boss

World "NormalDef"
Title "Normal Subgroups"
Introduction
"
A subgroup `N` of `G` is **normal** if it is closed under conjugation:
for every `n ∈ N` and every `g ∈ G`, we have `g * n * g⁻¹ ∈ N`.

Not every subgroup is normal — but every **kernel** of a homomorphism
is. That's the main theorem of this world.

Normal subgroups are the key to building **quotient groups**: the
construction `G / N` only makes sense when `N` is normal. Without
normality, coset multiplication is not well-defined.

Along the way, you'll learn the `have` tactic for introducing
intermediate results — an essential tool for building longer proofs.
"
