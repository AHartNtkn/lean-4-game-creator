import Game.Levels.ImageWorld.L01_ImageMembership
import Game.Levels.ImageWorld.L02_DestructuringImage
import Game.Levels.ImageWorld.L03_RintroRcases
import Game.Levels.ImageWorld.L04_ImageEmpty
import Game.Levels.ImageWorld.L05_ImageSingleton
import Game.Levels.ImageWorld.L06_ImageMonotonicity
import Game.Levels.ImageWorld.L07_ImageUnion
import Game.Levels.ImageWorld.L08_ImageInterSubset
import Game.Levels.ImageWorld.L09_IntersectionCounterexample
import Game.Levels.ImageWorld.L10_ImageComposition
import Game.Levels.ImageWorld.L11_SetRange
import Game.Levels.ImageWorld.L12_ImageUnivRange
import Game.Levels.ImageWorld.L13_GaloisConnection
import Game.Levels.ImageWorld.L14_ImagePreimageGap
import Game.Levels.ImageWorld.L15_PreimageImageGap
import Game.Levels.ImageWorld.L16_MonoFromGalois
import Game.Levels.ImageWorld.L17_GapFromGalois
import Game.Levels.ImageWorld.L18_NonemptinessTransfer
import Game.Levels.ImageWorld.L19_NonemptinessConverse
import Game.Levels.ImageWorld.L20_Boss

World "ImageWorld"
Title "Image World"

Introduction "
# Image World

You have mastered preimages -- pulling sets back through functions. Now you
will study the dual operation: **images** -- pushing sets forward.

Given a function `f : α → β` and a set `s : Set α` (a set of inputs),
the **image** of `s` under `f` is the set of all outputs that come from
inputs in `s`:

$$f(s) = \\{y \\mid \\exists\\, x \\in s,\\; f(x) = y\\}$$

In Lean, this is written `f '' s` (type `''`).

**The critical difference from preimage**: Image membership involves an
**existential**. To prove `y ∈ f '' s`, you must **exhibit a witness** --
an input `x ∈ s` such that `f x = y`. Preimage membership was just
function application (`x ∈ f ⁻¹' t ↔ f x ∈ t` -- no witness needed).
Image membership requires a construction.

This existential has far-reaching consequences:
- Image preserves union: **yes** (equality)
- Image preserves intersection: **no** (only ⊆, not =)
- Image preserves complement: **no**

Compare with preimage, which preserves ALL set operations. The
difference comes down to logic: preimage uses `∧`, `∨`, `¬` which
commute with function application. Image uses `∃`, which does NOT
commute with `∧` or `¬`.

By the end of this world, you will:
- Prove image membership by exhibiting witnesses
- Learn `rintro` and `rcases` -- power tools for pattern matching
- Prove `f '' ∅ = ∅` -- the vacuous extremal case
- Prove `f '' {a} = {f a}` -- the simplest image
- Prove image preserves union but NOT intersection
- See a concrete counterexample for intersection equality
- Prove image distributes over function composition
- Learn `Set.range` -- the image of everything
- Prove that `f '' Set.univ = Set.range f`
- Prove the Galois connection: `f '' s ⊆ t ↔ s ⊆ f ⁻¹' t`
- Explore the image-preimage gaps and when they close
- Re-derive monotonicity AND the image-preimage gap from the Galois connection
- Prove image preserves nonemptiness (both directions)

The boss asks you to prove that `f '' (f ⁻¹' t) = t` when every element
of `t` is in the range of `f` -- the image-preimage gap closes with a
surjectivity condition.

**New notation**: `f '' s` (typed `''`) -- the image of `s` under `f`.

**New tactics**: `rintro` and `rcases` -- pattern-matching introduction
and case analysis. You will also use `obtain` (from Set World) extensively
with a new pattern: `obtain ⟨x, hx, rfl⟩ := hy`.

**Prerequisites**: Set World, Subset World, Set Operations World,
Preimage World.
"
