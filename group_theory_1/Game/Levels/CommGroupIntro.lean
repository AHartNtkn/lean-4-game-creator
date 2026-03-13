import Game.Levels.CommGroupIntro.L01_MulComm
import Game.Levels.CommGroupIntro.L02_CommRearrange
import Game.Levels.CommGroupIntro.L03_PowerNotation
import Game.Levels.CommGroupIntro.L04_OnePow
import Game.Levels.CommGroupIntro.L05_Interchange
import Game.Levels.CommGroupIntro.L06_Boss

World "CommGroupIntro"
Title "Commutative Groups"

Introduction
"
Welcome to **Commutative Groups**, where multiplication finally
obeys the rule you've been taking for granted since primary school:
`a * b = b * a`.

Not every group is commutative. The integers under addition are,
but the group of 2-by-2 invertible matrices under multiplication
is not. A group where `a * b = b * a` for all elements `a` and `b` is
called **abelian** (after Niels Henrik Abel) or **commutative**,
and Lean calls its type `CommGroup`.

In a `CommGroup`, you can freely rearrange products — shuffling
factors into whatever order is convenient. This unlocks results
that fail for general groups. The headline example: if `a` and `b`
commute, then `(a * b) ^ n = a ^ n * b ^ n`. In a non-commutative
group, this is false — try expanding `(a * b) ^ 2` in a general
group and you get `a * b * a * b`, which rearranges to
`a ^ 2 * b ^ 2` only if `b * a = a * b`.

Along the way, you'll learn the `^` (power) notation and the
`induction` tactic — which you already know from the Natural Number
Game, just re-introduced here for this game's inventory.

By Level 6, you'll prove the **power-of-a-product** theorem:

`(a * b) ^ n = a ^ n * b ^ n`

using induction and the tools from this world.
"
