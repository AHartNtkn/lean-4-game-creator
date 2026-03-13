import Game.Levels.HomPset.L01_SimpReentry
import Game.Levels.HomPset.L02_RangeMulMem
import Game.Levels.HomPset.L03_KernelConjugation
import Game.Levels.HomPset.L04_EquationToKernel
import Game.Levels.HomPset.L05_KernelPowers
import Game.Levels.HomPset.L06_SurjectiveIntoRange
import Game.Levels.HomPset.L07_Boss

World "HomPset"
Title "Homomorphism Problem Set"

Introduction
"
Welcome to the **Homomorphism Problem Set** — practice under reduced
scaffolding.

You have all the tools from the last two worlds: `map_mul`, `map_one`,
`map_inv`, `simp`, kernel and range membership lemmas, `specialize`,
`use`, `ext`, and `Function.Injective`.

No new theorems or tactics here (except `Function.Surjective` in the
final levels — the natural dual of `Function.Injective`). The focus
is applying familiar moves to fresh problem surfaces.

The boss: prove that a homomorphism is surjective if and only if its
range is the whole group — the dual of the Kernel and Image boss:

| Property | Subgroup condition |
|----------|--------------------|
| **Injective** | `ker(f) = ⊥` (proved!) |
| **Surjective** | `range(f) = ⊤` (your target) |
"
