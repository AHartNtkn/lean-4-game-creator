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
import Game.Levels.BinomialCoefficients
import Game.Levels.Powerset
import Game.Levels.BinomialTheorem

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

-- Phase 1: Finite Types
Dependency MeetFin → FinNavigation → FinTuples → PsetFin
Dependency MeetFin → PsetFin
Dependency FinNavigation → PsetFin

-- Phase 2: Finite Sets (starts from W03)
Dependency FinTuples → FinsetBasics → FinsetOperations → FinsetImage → PsetFinset
Dependency FinsetBasics → PsetFinset
Dependency FinsetOperations → PsetFinset

-- Phase 3: Cardinality
Dependency FinsetImage → Cardinality → AbstractionLadder → Fintype → CountingTypes → PsetCardinality
Dependency Cardinality → PsetCardinality
Dependency AbstractionLadder → PsetCardinality
Dependency Fintype → PsetCardinality

-- Phase 4: Big Operators (starts from W06)
Dependency FinsetOperations → BigOpIntro → BigOpAlgebra → FinsetInduction → SummationFormulas → PsetBigOp
Dependency BigOpIntro → PsetBigOp
Dependency BigOpAlgebra → PsetBigOp
Dependency FinsetInduction → PsetBigOp

-- Phase 5: Combinatorics (cross-phase dependencies)
Dependency SummationFormulas → BinomialCoefficients
Dependency Cardinality → BinomialCoefficients
Dependency BinomialCoefficients → Powerset
Dependency Powerset → BinomialTheorem
Dependency BigOpAlgebra → BinomialTheorem

MakeGame
