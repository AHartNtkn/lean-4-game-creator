import GameServer.Commands
import Mathlib

World "FinIntro"
Level 7

Title "Distinct elements of Fin 3"

Introduction
"
# Concretizing `Fin n`

So far you have worked with the boundary cases `Fin 0` (empty) and `Fin 1`
(singleton). Let's now look at a type with more than one element.

`Fin 3` has exactly three elements: `0`, `1`, and `2`. These are distinct --
no two of them are the same.

## Your task

Prove that `(0 : Fin 3) ≠ (1 : Fin 3)`.

The tactic `intro h` will introduce the hypothesis `h : (0 : Fin 3) = (1 : Fin 3)`
and change the goal to `False`. Then you need to derive a contradiction.

One approach: `have hv := congr_arg Fin.val h` extracts `0 = 1` at the `Nat`
level, then `omega` spots the contradiction.

A simpler approach: after `intro h`, try `exact absurd h (by omega)`.
The `omega` tactic can decide the negation `(0 : Fin 3) ≠ (1 : Fin 3)`
directly.

Or simplest of all: `omega` can handle the entire goal in one step, since
inequality of `Fin` literals reduces to inequality of natural numbers.
"

/-- The elements `0` and `1` of `Fin 3` are distinct. -/
Statement : (0 : Fin 3) ≠ (1 : Fin 3) := by
  Hint "The simplest approach: `omega` can handle `Fin` literal inequalities directly."
  Hint (hidden := true) "You can also start with `intro h` to assume they are equal, then derive
  a contradiction. After `intro h`, try `exact absurd (congr_arg Fin.val h) (by omega)`."
  omega

Conclusion
"
`Fin 3` has three distinct elements: `0`, `1`, and `2`. You just proved
that two of them are different.

The mental model you should carry forward: **`Fin n` is the set
$\\{0, 1, \\ldots, n-1\\}$**. It has exactly `n` elements, they are
zero-indexed, and they are all distinct.

This proposition is *decidable* -- there is a procedure that can check it
mechanically. In the next world, you will learn the `decide` tactic, which
automates this kind of reasoning.

In the next world (W3_ex), you will work extensively with `Fin 3` as
a concrete object -- enumerating its elements, building functions on it,
and proving properties by exhaustion. For now, the key takeaway is that
`Fin n` is not just an abstract subtype -- it is a concrete, finite set
that you can reason about element by element.
"
