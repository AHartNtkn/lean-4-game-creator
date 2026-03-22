import GameServer.Commands

import Game.Levels.MeetFin
import Game.Levels.FinNavigation
import Game.Levels.FinTuples
import Game.Levels.PsetFin
import Game.Levels.FinsetBasics
import Game.Levels.FinsetOperations
import Game.Levels.FinsetImage
import Game.Levels.PsetFinset
import Game.Levels.Cardinality
import Game.Levels.AbstractionLadder
import Game.Levels.Fintype
import Game.Levels.CountingTypes
import Game.Levels.PsetCardinality
import Game.Levels.BigOpIntro
import Game.Levels.BigOpAlgebra
import Game.Levels.FinsetInduction
import Game.Levels.SummationFormulas
import Game.Levels.PsetBigOp

Title "Finite Mathematics"
Introduction
"
# Finite Mathematics

Finite sets, finsets, multisets, lists, and finite sums/products.

This course covers the finite-object infrastructure: `Fin`, `Fintype`, `Finset`,
finite sets as subtypes, lists versus multisets, permutations of lists, finitely
supported functions, big operators, matrices over finite index types, binomial
coefficients, factorials, and counting identities.

This course is under construction.
"

Dependency MeetFin → FinNavigation → FinTuples → PsetFin → FinsetBasics → FinsetOperations → FinsetImage → PsetFinset → Cardinality → AbstractionLadder → Fintype → CountingTypes → PsetCardinality → BigOpIntro → BigOpAlgebra → FinsetInduction → SummationFormulas → PsetBigOp

MakeGame
