import GameServer.Commands
import Game.Levels.Welcome
import Game.Levels.FinIntro
import Game.Levels.FinCompute
import Game.Levels.ListBasics
import Game.Levels.FinThreeExamples
import Game.Levels.MultisetHierarchy
import Game.Levels.ListUnderLenses
import Game.Levels.FinsetConstructors
import Game.Levels.FinsetMembership
import Game.Levels.FinsetOperations
import Game.Levels.FinsetTransformations
import Game.Levels.FinsetExploration
import Game.Levels.FinsetCardinality
import Game.Levels.FinsetInduction
import Game.Levels.FinsetPset
import Game.Levels.FintypeClass
import Game.Levels.CountingPigeonhole
import Game.Levels.CountingFunctions
import Game.Levels.CountingPset
import Game.Levels.FinsetSum
import Game.Levels.RangeSumInduction
import Game.Levels.SumFormula
import Game.Levels.FinsetProd
import Game.Levels.BigOpAdvanced
import Game.Levels.BigOpPset
import Game.Levels.Factorials
import Game.Levels.BinomialCoefficients
import Game.Levels.PascalsTriangle
import Game.Levels.BinomialTheorem
import Game.Levels.CombinatorialPset
import Game.Levels.ThreeFiniteness
import Game.Levels.FinsuppWorld
import Game.Levels.PermutationWorld
import Game.Levels.MatrixWorld
import Game.Levels.Capstone

Title "Finite Mathematics"
Introduction
"
# Finite Mathematics

Finite sets, finsets, multisets, lists, and finite sums/products.

This course covers the finite-object infrastructure: `Fin`, `Fintype`, `Finset`,
finite sets as subtypes, lists versus multisets, permutations of lists, finitely
supported functions, big operators, matrices over finite index types, binomial
coefficients, factorials, and counting identities.
"

Dependency Welcome → FinIntro
Dependency FinIntro → FinCompute
Dependency FinIntro → ListBasics
Dependency FinCompute → FinThreeExamples
Dependency ListBasics → MultisetHierarchy
Dependency MultisetHierarchy → ListUnderLenses
Dependency ListUnderLenses → FinsetConstructors
Dependency FinsetConstructors → FinsetMembership
Dependency FinsetMembership → FinsetOperations
Dependency FinsetOperations → FinsetTransformations
Dependency FinsetTransformations → FinsetExploration
Dependency FinsetExploration → FinsetCardinality
Dependency FinsetCardinality → FinsetInduction
Dependency FinsetInduction → FinsetPset
Dependency FinsetPset → FintypeClass
Dependency FinCompute → FintypeClass
Dependency FintypeClass → CountingPigeonhole
Dependency CountingPigeonhole → CountingFunctions
Dependency CountingPigeonhole → CountingPset
Dependency FinsetInduction → FinsetSum
Dependency FinsetSum → RangeSumInduction
Dependency RangeSumInduction → SumFormula
Dependency RangeSumInduction → FinsetProd
Dependency FinsetProd → BigOpAdvanced
Dependency BigOpAdvanced → BigOpPset
Dependency BigOpAdvanced → Factorials
Dependency CountingPigeonhole → Factorials
Dependency Factorials → BinomialCoefficients
Dependency BinomialCoefficients → PascalsTriangle
Dependency PascalsTriangle → BinomialTheorem
Dependency BinomialTheorem → CombinatorialPset
Dependency FintypeClass → ThreeFiniteness
Dependency ThreeFiniteness → FinsuppWorld
Dependency BigOpAdvanced → FinsuppWorld
Dependency ThreeFiniteness → PermutationWorld
Dependency CountingPigeonhole → PermutationWorld
Dependency PermutationWorld → MatrixWorld
Dependency BigOpAdvanced → MatrixWorld
Dependency MatrixWorld → Capstone
Dependency FinsuppWorld → Capstone
Dependency BinomialTheorem → Capstone

MakeGame
