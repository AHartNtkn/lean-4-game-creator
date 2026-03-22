import Game.Levels.FinTuples.L01_FunctionsAsTuples
import Game.Levels.FinTuples.L02_VecNotation
import Game.Levels.FinTuples.L03_BuildingTuples
import Game.Levels.FinTuples.L04_PrependingWithCons
import Game.Levels.FinTuples.L05_ConsAccessLemmas
import Game.Levels.FinTuples.L06_DroppingTheHead
import Game.Levels.FinTuples.L07_HeadTailReconstruction
import Game.Levels.FinTuples.L08_RoundTripProperty
import Game.Levels.FinTuples.L09_AppendingWithSnoc
import Game.Levels.FinTuples.L10_DroppingTheLast
import Game.Levels.FinTuples.L11_InitSnocReconstruction
import Game.Levels.FinTuples.L12_ExtForFunctions
import Game.Levels.FinTuples.L13_TupleComposition
import Game.Levels.FinTuples.L14_TuplesAsData
import Game.Levels.FinTuples.L15_ConsInjectivity
import Game.Levels.FinTuples.L16_SnocInjectivity
import Game.Levels.FinTuples.L17_TheEmptyTuple
import Game.Levels.FinTuples.L18_ProvingTupleEquality
import Game.Levels.FinTuples.L19_FlippingEquations
import Game.Levels.FinTuples.L20_ReconstructionStrategy
import Game.Levels.FinTuples.L21_Boss

World "FinTuples"
Title "Fin Tuples"

Introduction "
# Fin Tuples: Functions as Ordered Data

You've learned that `Fin n` is the finite index set
$\\{0, 1, \\ldots, n-1\\}$, and you can navigate within it using
`last`, `castSucc`, and `succ`. Now comes the payoff:

**A function `Fin n → α` is an `n`-tuple.**

This is one of the most useful identifications in formalized
mathematics. A vector in $\\mathbb{R}^3$ is a function
`Fin 3 → ℝ`. A sequence of length 5 is a function
`Fin 5 → α`. The entries of an $n \\times m$ matrix are a
function `Fin n → Fin m → ℝ`.

The advantage of using functions instead of lists: the length
is part of the type. You can't accidentally add a 3-vector to
a 4-vector — the types don't match.

In this world, you'll learn to:
- **Build** tuples using `![a, b, c]` notation and `Fin.cons`
- **Append** elements using `vecSnoc`
- **Decompose** from both ends: `Fin.tail` (drop first) and `Fin.init` (drop last)
- **Reconstruct**: `Fin.cons_self_tail` (from front) and `vecSnoc_self_init` (from back)
- **Transform** tuples via function composition
- **Use** tuples as data: verify concrete computations
- **Prove** two tuples are equal using function extensionality (`ext`)
- **Flip** equations with `.symm` for reconstruction proofs

The central tool is **`ext`**: two tuples are equal if and only
if they agree at every index. You already know `ext` for `Fin`
elements (two `Fin` values are equal when their natural numbers
are equal). Here, `ext` says two functions are equal when they
agree on all inputs — same tactic, new context.

The boss at the end will ask you to prove two differently-described
tuples are equal, combining reconstruction from both ends with
extensionality in a single proof.
"
