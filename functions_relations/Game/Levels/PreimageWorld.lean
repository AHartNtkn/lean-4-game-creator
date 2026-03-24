import Game.Levels.PreimageWorld.L01_PreimageMembership
import Game.Levels.PreimageWorld.L02_PreimageNonMembership
import Game.Levels.PreimageWorld.L03_PreimageNonInjective
import Game.Levels.PreimageWorld.L04_PreimageSingleton
import Game.Levels.PreimageWorld.L05_PreimageMonotonicity
import Game.Levels.PreimageWorld.L06_PreimageEmpty
import Game.Levels.PreimageWorld.L07_PreimageUniv
import Game.Levels.PreimageWorld.L08_PreimageIntersection
import Game.Levels.PreimageWorld.L09_PreimageUnion
import Game.Levels.PreimageWorld.L10_PreimageComplement
import Game.Levels.PreimageWorld.L11_PreimageIndexedUnion
import Game.Levels.PreimageWorld.L12_PreimageIndexedIntersection
import Game.Levels.PreimageWorld.L13_PreimageIdentity
import Game.Levels.PreimageWorld.L14_PreimageComposition
import Game.Levels.PreimageWorld.L15_RewriteComposition
import Game.Levels.PreimageWorld.L16_Boss

World "PreimageWorld"
Title "Preimage World"

Introduction "
# Preimage World

Given a function `f : α → β` and a set `t : Set β` (a set of outputs),
the **preimage** of `t` under `f` is the set of all inputs whose output
lands in `t`:

$$f^{-1}(t) = \\{x \\mid f(x) \\in t\\}$$

In Lean, this is written `f ⁻¹' t` (type `\\-1'`).

Preimage is defined by a single, beautiful principle:
**membership in a preimage is function application followed by a
membership check.** Nothing more. There is no existential, no witness,
no construction — just \"apply `f`, then check if the result is in `t`.\"

This simplicity has a remarkable consequence: **preimage preserves
every set operation**. Intersection, union, complement, difference,
indexed unions, indexed intersections — they all distribute over
preimage. The logical connectives (`∧`, `∨`, `¬`, `∃`, `∀`) pass
through function application unchanged.

By the end of this world, you will:
- Prove concrete preimage membership by computing `f x`
- See why non-injective functions make preimage interesting
- Learn the **fiber** vocabulary (preimage of a singleton)
- Prove preimage is monotone (bigger target → bigger preimage)
- Prove preimage preserves `∅`, `Set.univ`, `∩`, `∪`, `ᶜ`, `⋃`, `⋂`, and `\\`
- Prove the functor laws: identity and composition reversal
- Learn to **compose library results** via sequential `rw`
- Understand WHY preimage is so well-behaved (it is just composition)

The boss asks you to prove that preimage preserves set difference —
by **composing** the intersection and complement results you proved
earlier.

**New notation**: `f ⁻¹' t` (typed `\\-1'`) — the preimage of `t`
under `f`.

**Prerequisites**: Set World, Subset World, Set Operations World,
Indexed Operations World.
"
