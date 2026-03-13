import Game.Levels.HomComposition.L01_CompApply
import Game.Levels.HomComposition.L02_KerContainment
import Game.Levels.HomComposition.L03_RangeContainment
import Game.Levels.HomComposition.L04_CompInjective
import Game.Levels.HomComposition.L05_CompSurjective
import Game.Levels.HomComposition.L06_CoachLiftEquation
import Game.Levels.HomComposition.L07_Boss

World "HomComposition"
Title "Homomorphism Composition"

Introduction
"
Welcome to **Homomorphism Composition**.

You know how to reason about individual homomorphisms — pushing `f`
through products, reasoning about kernels and ranges, and connecting
injectivity to trivial kernel.

Now: what happens when you **chain** two homomorphisms?

Given `f : G →* H` and `g : H →* K`, their composition
`g.comp f : G →* K` maps `x` to `g(f(x))`. This is itself a
group homomorphism — the composition of hom-respecting maps
respects the group operation.

The central questions of this world:
- How do the kernel and range of `g ∘ f` relate to those of
  `f` and `g` individually?
- If the composition is injective, what does that say about `f`?
  About `g`?
- If the composition is surjective, what does that say about `f`?
  About `g`?

The key insight is an **asymmetry**: injectivity of `g ∘ f` tells
you about `f` (the inner map), while surjectivity of `g ∘ f` tells
you about `g` (the outer map). The boss theorem is:

> **`g ∘ f` injective implies `f` injective.**
"
