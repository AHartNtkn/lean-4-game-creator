import Game.Levels.PsetFin.L01_DoubleWitness
import Game.Levels.PsetFin.L02_CastSuccNeverLast
import Game.Levels.PsetFin.L03_SnocReconstruction
import Game.Levels.PsetFin.L04_AntisymmetricEquality
import Game.Levels.PsetFin.L05_PointwiseFormula
import Game.Levels.PsetFin.L06_VacuousTruth
import Game.Levels.PsetFin.L07_SuccNeverZero
import Game.Levels.PsetFin.L08_ObtainDestructure
import Game.Levels.PsetFin.L09_ZeroSuccRetrieval
import Game.Levels.PsetFin.L10_ModularEquality
import Game.Levels.PsetFin.L11_GeneralDecomposition
import Game.Levels.PsetFin.L12_GeneralZeroSuccDecomposition
import Game.Levels.PsetFin.L13_SuccAboveUnification
import Game.Levels.PsetFin.L14_CyclicPermutation
import Game.Levels.PsetFin.L15_ObtainMeetsDecomposition
import Game.Levels.PsetFin.L16_SimplePigeonhole
import Game.Levels.PsetFin.L17_Pigeonhole
import Game.Levels.PsetFin.L18_Boss

World "PsetFin"
Title "Problem Set: Fin"

Introduction "
# Problem Set: Fin Types

You've completed three lecture worlds on `Fin`:
- **MeetFin**: constructing and comparing elements
- **FinNavigation**: moving between types with `succ`, `castSucc`, `last`
- **FinTuples**: building and decomposing tuples with `cons`, `snoc`, `ext`

Now prove theorems using these skills on **fresh problems** — no
new definitions, sparser hints, and one new tactic (`obtain`,
introduced midway through).

If you get stuck, ask yourself:
- Is the goal about **Fin elements being equal**? → try `ext`
- Is the goal about **functions being equal**? → try `ext`
- Is the goal about **values**? → try val lemmas + `omega`
- Do you need to **enumerate cases**? → destructure + case split
- Can you **reconstruct** a tuple from its parts? → `cons_self_tail` or `vecSnoc_self_init`
- Is the type **Fin 0**? → `Fin.elim0` eliminates any element
- Do you have an **existential hypothesis**? → `obtain ⟨j, hj⟩ := h`
"
