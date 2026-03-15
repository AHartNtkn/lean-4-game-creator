import GameServer.Commands
import Mathlib

World "FinIntro"
Level 5

Title "Fin 0 is empty"

Introduction
"
# The empty type `Fin 0`

What natural numbers are less than `0`? None!

This means `Fin 0` has **no elements at all**. It is an empty type.

If someone gives you an element `h : Fin 0`, they have given you something
that cannot exist. From a false premise, you can prove anything -- this is
the principle of **ex falso** (\"from falsehood, anything follows\").

## The proof move

Rather than memorizing a magic function, let's discover *why* `Fin 0` is
impossible. If `h : Fin 0`, then `h` carries a proof `h.isLt` that
`h.val < 0`. But no natural number is less than `0`!

Here is the plan:
1. Extract the impossible fact with `have h_lt := h.isLt`
2. The `omega` tactic recognizes that `h.val < 0` is a contradiction
   among natural numbers and closes the goal

## Your task

Prove that if you have an element of `Fin 0`, you can derive `False`.

**Misconception alert (C5)**: `Fin 0` is empty -- it has zero elements.
`Fin 1` has one element (namely `0`). Don't confuse the index with the
number of elements!
"

/-- `Fin 0` has no elements. -/
Statement (h : Fin 0) : False := by
  Hint "First, extract the impossible bound. Try `have h_lt := h.isLt`."
  have h_lt := h.isLt
  Hint "Now `h_lt : h.val < 0` is in your context. No natural number is less
  than 0, so this is a contradiction. The `omega` tactic can see this. Try `omega`."
  omega

Conclusion
"
You discovered the proof from first principles: `h.isLt` says `h.val < 0`,
and no natural number satisfies that, so `omega` derives a contradiction.

In practice, mathlib provides `Fin.elim0` which packages exactly this argument.
So `exact h.elim0` or `exact Fin.elim0 h` also work. But understanding *why*
it works -- that the bound `val < 0` is impossible -- is more valuable than
memorizing the function name.

This is an important boundary case. In many proofs about `Fin n`, the
case `n = 0` needs special handling because there are no elements to
work with. You have just handled the base case. In the next few levels,
you will see how `Fin (n+1)` decomposes into `Fin n` plus one extra
element -- the inductive step.

**In plain language**: \"If someone claims to have a natural number
less than zero, they are mistaken, and from their mistake we can
conclude anything.\"
"

/-- `Fin.elim0` derives anything from an element of `Fin 0`. Since `Fin 0` is
empty, this is the principle of ex falso for the empty finite type.
Usage: `exact Fin.elim0 h` or `exact h.elim0`. -/
TheoremDoc Fin.elim0 as "Fin.elim0" in "Fin"

NewTheorem Fin.elim0
