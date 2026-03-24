import Game.Levels.InjectiveWorld.L01_InjectiveIntro
import Game.Levels.InjectiveWorld.L02_InjectiveDoubling
import Game.Levels.InjectiveWorld.L03_NonInjective
import Game.Levels.InjectiveWorld.L04_Composition
import Game.Levels.InjectiveWorld.L05_Extraction
import Game.Levels.InjectiveWorld.L06_RewritingCoaching
import Game.Levels.InjectiveWorld.L07_LeftInverse
import Game.Levels.InjectiveWorld.L08_Boss

World "InjectiveWorld"
Title "Injective World"

Introduction "
# Injective World

A function is **injective** (one-to-one) if it never sends two different
inputs to the same output. In Lean:

$$\\text{Injective}(f) \\;\\;:\\equiv\\;\\; \\forall\\, a\\, b,\\;\\; f(a) = f(b) \\;\\Longrightarrow\\; a = b$$

This is one of the most fundamental properties of functions. Injective
functions preserve distinctness — they never \"collapse\" information.

In Pset: Images & Preimages, you already used `Function.Injective` as
a hypothesis to close gaps in image–set-operation identities. Now you will
learn to **prove** injectivity from scratch, and to **compose** and
**extract** injectivity across function compositions.

By the end of this world, you will:
- Prove injectivity using the canonical proof shape: `intro a b hab` → derive `a = b`
- Disprove injectivity by exhibiting a counterexample
- Prove that composition preserves injectivity
- Extract injectivity of `f` from injectivity of `g ∘ f`
- Learn to rewrite at hypotheses and use backward rewriting
- Prove that a left inverse implies injectivity
- Integrate these skills in the boss

**New definitions**: `Function.Injective`, `Function.LeftInverse`

**Prerequisites**: Set World (for `show`, `omega`, `have`).
"
