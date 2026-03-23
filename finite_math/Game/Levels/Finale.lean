import Game.Levels.Finale.L01_InductionIdentity
import Game.Levels.Finale.L02_PowersetPartition
import Game.Levels.Finale.L03_DiagonalDecomposition
import Game.Levels.Finale.L04_FiberTemplate
import Game.Levels.Finale.L05_QuantitativePigeonhole
import Game.Levels.Finale.L06_NonInjectivity
import Game.Levels.Finale.L07_ConcretePigeonhole
import Game.Levels.Finale.L08_SubsetEquality
import Game.Levels.Finale.L09_DoubleCounting
import Game.Levels.Finale.L10_FinsuppIntegration
import Game.Levels.Finale.L11_FinsetInductionIntegration
import Game.Levels.Finale.L12_MatrixIntegration
import Game.Levels.Finale.L13_SurjectiveImpliesInjective
import Game.Levels.Finale.L14_Boss
import Game.Levels.Finale.L15_InfiniteCounterexample
import Game.Levels.Finale.L16_EquivalenceBiconditional

World "Finale"
Title "Finale"

Introduction "
# Finale

You've built the complete finite mathematics toolkit across
seven phases:

1. **Finite types** — `Fin n`, navigation, tuples
2. **Finite sets** — `Finset`, membership, operations, image
3. **Cardinality** — `Fintype.card`, type decomposition, counting types
4. **Big operators** — `∑`, `∏`, induction, summation formulas
5. **Combinatorics** — binomial coefficients, powerset, Pascal's triangle
6. **Advanced structures** — products, finitely supported functions, matrices
7. **Counting techniques** — bijection, injection, pigeonhole, double counting

This final world integrates techniques from multiple phases into
thirteen coaching levels, one boss, and two epilogue levels. Each
coaching level exercises a different combination of tools:

**Levels**:
1. A new summation formula by induction (Phase 4)
2. Powerset partition by size (Phases 4+5)
3. Diagonal decomposition of self-products (Phases 2+6)
4. The fiber template on Fin types (Phases 1+3+7)
5. Quantitative pigeonhole via fiber bounding (Phases 1+3+4+7)
6. Non-injectivity via image cardinality (Phases 2+3)
7. Pigeonhole applied to modular arithmetic (concrete application)
8. Subset equality via cardinality (Phases 2+3 — seeds the boss)
9. Three-part set decomposition (Phases 2+3 — double counting)
10. Support bounding via calc chain (Phases 2+3+6)
11. Sum distributes over addition by finset induction (Phase 4)
12. Trace of the identity matrix (Phases 3+4+6)
13. Surjective implies injective for finite types (Phases 2+3+7)
14. **Boss**: prove injective endofunctions are surjective (Phases 2+3+7)
15. The infinite counterexample: why finiteness is essential
16. Bijective from injective: the course capstone
"
