import Game.Levels.NormalPset.L01_IntersectionConjugation
import Game.Levels.NormalPset.L02_DeConjugation
import Game.Levels.NormalPset.L03_Contradiction
import Game.Levels.NormalPset.L04_ProductConjugation
import Game.Levels.NormalPset.L05_CyclicPermutation
import Game.Levels.NormalPset.L06_CosetShift
import Game.Levels.NormalPset.L07_ContradictionPractice
import Game.Levels.NormalPset.L08_Boss

World "NormalPset"
Title "Normal Subgroups Problem Set"
Introduction
"
Welcome to the **Normal Subgroups Problem Set** — practice under
reduced scaffolding.

You have all the tools from the last world: the `Normal` definition,
`conj_mem` and `conj_mem'`, coset membership lemmas, and the `have`
tactic. This world exercises them on fresh surfaces.

You'll also learn one new tool: `contradiction`, which closes a goal
when your hypotheses contradict each other.

The boss: prove that the intersection of two normal subgroups is
normal — combining the Normal constructor with component-wise
reasoning from the Subgroup Basics world.
"
