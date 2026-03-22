import Game.Levels.FinNavigation.L01_TheLastElement
import Game.Levels.FinNavigation.L02_LastIsMaximum
import Game.Levels.FinNavigation.L03_EmbeddingCastSucc
import Game.Levels.FinNavigation.L04_MovingForwardSucc
import Game.Levels.FinNavigation.L05_CastSuccBelowSucc
import Game.Levels.FinNavigation.L06_CastSuccNeSucc
import Game.Levels.FinNavigation.L07_CastSuccNeverLast
import Game.Levels.FinNavigation.L08_CastSuccInjectivity
import Game.Levels.FinNavigation.L09_SuccInjectivity
import Game.Levels.FinNavigation.L10_ZeroSuccDecomposition
import Game.Levels.FinNavigation.L11_SuccNeverZero
import Game.Levels.FinNavigation.L12_RecognizingLast
import Game.Levels.FinNavigation.L13_FindingCastSucc
import Game.Levels.FinNavigation.L14_Surjectivity
import Game.Levels.FinNavigation.L15_SuccSurjectivity
import Game.Levels.FinNavigation.L16_Boss

World "FinNavigation"
Title "Fin Navigation"

Introduction "
# Navigating Fin

You've learned to construct and compare elements of `Fin n`. Now
you'll learn to *navigate* within `Fin n` — accessing specific
landmark elements and moving between `Fin n` and `Fin (n+1)`.

Three functions form the navigation toolkit:

**`Fin.last n`** — the maximum element of `Fin (n+1)`, with
value `n`. It's the boundary element, sitting at the top.

**`Fin.castSucc`** — embeds `Fin n` into `Fin (n+1)` by keeping
the same value but relaxing the bound. If `i : Fin n` has value
`k`, then `i.castSucc : Fin (n+1)` also has value `k`.

**`Fin.succ`** — moves forward: if `i : Fin n` has value `k`,
then `i.succ : Fin (n+1)` has value `k + 1`.

Both `castSucc` and `succ` send `Fin n → Fin (n+1)` — they
increase the type's size by 1 — but they do different things to
the value: `castSucc` preserves it, `succ` increments it.

(This is why `Fin n` starts at 0: the embedding `castSucc`
preserves values exactly, and `succ` increments by exactly 1. With
1-indexing, these clean relationships would need offsets.)

The central insight of this world: `Fin (n+1)` has **two**
decompositions:
- Every element is either `Fin.last n` or `j.castSucc`
  for some `j : Fin n` (**castSucc/last**)
- Every element is either `0` or `j.succ`
  for some `j : Fin n` (**0/succ**)

These dual decompositions will power the two ways to build
tuples in the next world.

In this world, you'll learn to:
- Compute the value of `last`, `castSucc`, and `succ` using their
  val lemmas
- Prove that `castSucc` never reaches `last` (and `succ` never
  reaches `0`)
- Prove that both `castSucc` and `succ` are injective
- Prove both the castSucc/last and 0/succ decompositions
- Prove that `castSucc` hits every non-last element (surjectivity)
- Combine all of this in the boss
"
