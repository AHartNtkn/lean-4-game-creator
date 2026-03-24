import Game.Levels.SurjectiveWorld.L01_SurjectiveIntro
import Game.Levels.SurjectiveWorld.L02_NonSurjective
import Game.Levels.SurjectiveWorld.L03_DomainDependence
import Game.Levels.SurjectiveWorld.L04_SurjectivePractice
import Game.Levels.SurjectiveWorld.L05_ProjectionSurjectivity
import Game.Levels.SurjectiveWorld.L06_RangeCharacterization
import Game.Levels.SurjectiveWorld.L07_RangeCharBackward
import Game.Levels.SurjectiveWorld.L08_ImagePreimageEquality
import Game.Levels.SurjectiveWorld.L09_Composition
import Game.Levels.SurjectiveWorld.L10_Extraction
import Game.Levels.SurjectiveWorld.L11_RightCancelation
import Game.Levels.SurjectiveWorld.L12_Counterexample
import Game.Levels.SurjectiveWorld.L13_RightInverse
import Game.Levels.SurjectiveWorld.L14_ConstructRightInverse
import Game.Levels.SurjectiveWorld.L15_StrategicWitness
import Game.Levels.SurjectiveWorld.L16_Boss

World "SurjectiveWorld"
Title "Surjective World"

Introduction "
# Surjective World

A function is **surjective** (onto) if every element of the codomain is
the image of at least one element of the domain. In Lean:

$$\\text{Surjective}(f) \\;\\;:\\equiv\\;\\; \\forall\\, b,\\;\\; \\exists\\, a,\\;\\; f(a) = b$$

**Why surjectivity matters**: A function `f` is surjective when the
equation `f(x) = b` always has a solution — no matter which `b` you
pick. This makes surjections central to algebra (solvability of
equations), topology (quotient maps), and the foundations of mathematics
(the Axiom of Choice is equivalent to the statement that every surjection
has a right inverse).

Surjectivity is the dual of injectivity. While an injective function
never collapses two inputs to the same output, a surjective function
never misses an output — every possible result is achieved.

In Injective World, you mastered the proof shape `intro a b hab` →
derive `a = b`. Here you will master the dual shape: `intro b` →
find a witness `a` with `f a = b`.

By the end of this world, you will:
- Prove surjectivity using the canonical shape: `intro b` → `use witness` → verify
- Disprove surjectivity by exhibiting an unreachable output
- See that surjectivity depends on the domain, not just the formula
- Prove surjectivity for a structural (non-arithmetic) function
- Characterize surjectivity as `Set.range f = Set.univ`
- Prove that surjective image-preimage round trips recover the original set
- Prove that composition preserves surjectivity
- Extract surjectivity of `g` from surjectivity of `g ∘ f`
- Prove the right cancelation property (the algebraic characterization)
- Prove a concrete counterexample for the false converse
- Prove that a right inverse implies surjectivity
- Construct a right inverse from surjectivity using the Axiom of Choice
- Combine surjectivity with injectivity in the boss

**New definitions**: `Function.Surjective`, `Function.RightInverse`

**Prerequisites**: Injective World (for `Function.Injective`, `apply` chains,
and rewriting moves), Image World (for `Set.range`, `Set.mem_range`),
Set World (for `obtain`, `ext`).
"
