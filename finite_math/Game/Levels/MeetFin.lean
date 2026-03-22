import Game.Levels.MeetFin.L01_WhatIsFin
import Game.Levels.MeetFin.L02_TheNumberInside
import Game.Levels.MeetFin.L03_TheUpperBound
import Game.Levels.MeetFin.L04_ConstructionAndExtraction
import Game.Levels.MeetFin.L05_FinEquality
import Game.Levels.MeetFin.L06_ConverseDirection
import Game.Levels.MeetFin.L07_RewritingHypotheses
import Game.Levels.MeetFin.L08_TransferringBounds
import Game.Levels.MeetFin.L09_FinEta
import Game.Levels.MeetFin.L10_DerivingFinEta
import Game.Levels.MeetFin.L11_ProofIrrelevance
import Game.Levels.MeetFin.L12_BeyondConcreteTypes
import Game.Levels.MeetFin.L13_EmptyType
import Game.Levels.MeetFin.L14_ExplosionPrinciple
import Game.Levels.MeetFin.L15_UniqueElement
import Game.Levels.MeetFin.L16_DestructuringFin
import Game.Levels.MeetFin.L17_TwoElements
import Game.Levels.MeetFin.L18_CaseAnalysisPractice
import Game.Levels.MeetFin.L19_ModularArithmetic
import Game.Levels.MeetFin.L20_ConcreteApplication
import Game.Levels.MeetFin.L21_ProvingInequality
import Game.Levels.MeetFin.L22_ExistentialWitness
import Game.Levels.MeetFin.L23_Boss

World "MeetFin"
Title "Meet Fin"

Introduction "
# Meet Fin

Welcome to the world of finite types!

In mathematics, finite index sets like $\\{0, 1, \\ldots, n-1\\}$ appear
everywhere — as indices of vectors, as labels for vertices of a polygon,
as positions in a sequence. In Lean 4, this finite index set is called
`Fin n`.

An element of `Fin n` is not just a number — it's a number **bundled
with a proof** that it's less than `n`. This bundling is what makes
`Fin n` a proper type rather than just a naming convention. The
advantage: the type system enforces the bound for you, so out-of-range
indices are impossible to construct.

`Fin n` is a *subtype* of `ℕ` — the subtype `{ k : ℕ // k < n }`.
You'll see this subtype pattern again in later courses.

In this world, you'll learn to:
- **Construct** elements of `Fin n`
- **Extract** their natural number values
- **Prove** when two `Fin` elements are equal (or not!)
- **Handle** the edge cases `Fin 0` (empty!) and `Fin 1` (singleton)
- **Case-split** to reason about all elements of a small `Fin` type

Three warnings before we begin:
1. `Fin n` starts at **0**, not 1. The elements are $0, 1, \\ldots, n-1$.
   (Why? Because the defining predicate is `k < n` on `ℕ`, which
   naturally gives $\\{0, \\ldots, n-1\\}$.)
2. `Fin 0` is **empty**. There is no natural number less than 0.
3. Two `Fin` elements are equal when their **values** are equal — you
   need `Fin.ext_iff` to access this fact (you'll also learn the
   `ext` tactic later in this world).

The boss at the end will ask you to combine all these moves in a single
proof. Let's begin!
"
