import Game.Levels.CountingTechniques.L01_BijectiveCounting
import Game.Levels.CountingTechniques.L02_InjectionBound
import Game.Levels.CountingTechniques.L03_SurjectionBound
import Game.Levels.CountingTechniques.L04_BijectionEquality
import Game.Levels.CountingTechniques.L05_SurjectionApplication
import Game.Levels.CountingTechniques.L06_StrictSubset
import Game.Levels.CountingTechniques.L07_StrictInjectionBound
import Game.Levels.CountingTechniques.L08_Pigeonhole
import Game.Levels.CountingTechniques.L09_PigeonholeApplication
import Game.Levels.CountingTechniques.L10_PigeonholeTransfer
import Game.Levels.CountingTechniques.L11_FiberDecomposition
import Game.Levels.CountingTechniques.L12_UniformFibers
import Game.Levels.CountingTechniques.L13_FiberBound
import Game.Levels.CountingTechniques.L14_ConcreteDoubleCounting
import Game.Levels.CountingTechniques.L15_PushNeg
import Game.Levels.CountingTechniques.L16_AveragingArgument
import Game.Levels.CountingTechniques.L17_GeneralizedPigeonhole
import Game.Levels.CountingTechniques.L18_Practice
import Game.Levels.CountingTechniques.L19_Boss

World "CountingTechniques"
Title "Counting Techniques"

Introduction "
# Counting Techniques

You've built a complete finite mathematics toolkit: `Fin`, `Finset`,
`Fintype`, big operators, binomial coefficients, induction. Now
we learn the four major **proof techniques** for combinatorics:

1. **Bijective counting** — prove two sets have equal cardinality
   by exhibiting a bijection (`Equiv`)
2. **Injection/surjection bounds** — prove cardinality inequalities
   from injective or surjective functions
3. **The Pigeonhole Principle** — more items than containers forces
   a collision
4. **Double counting** (fiber decomposition) — count the same set
   two different ways

**Why these four?** They cover the natural landscape of counting
arguments:
- Bijective counting handles **equalities** (`|A| = |B|`)
- Injection/surjection bounds handle **inequalities** (`|A| <= |B|`)
- Pigeonhole is the **contrapositive** of injection bounds --
  it proves impossibility by contradiction
- Double counting **decomposes** a count into structured parts

Together they span: equal vs. unequal cardinality, direct vs.
indirect proof, and single-count vs. decomposed-count. Nearly
every counting argument in discrete mathematics reduces to one
of these four techniques, or -- as in the boss -- a combination.

**Levels**:
1. Bijective counting revisited
2. Injection gives a cardinality bound
3. Surjection gives a cardinality bound
4. Bijection = injection + surjection
5. Surjection bound in action
6. Strict subset means strictly fewer
7. Strict injection bound
8. The pigeonhole principle
9. Pigeonhole: finding a collision
10. From collision to non-injectivity
11. Double counting: fiber decomposition
12. Uniform fibers: multiplication principle
13. Bounding with non-uniform fibers
14. Concrete double counting
15. Pushing negations with push_neg
16. The averaging argument
17. Generalized pigeonhole
18. Practice: mutual injection principle
19. Boss: counting technique integration
"
