import GameServer.Commands
import Mathlib

World "FinIntro"
Level 2

Title "Extracting the value"

Introduction
"
# `Fin.val` -- getting the number out

Every element `i : Fin n` carries two pieces of information:
- `i.val : Nat` -- the underlying natural number
- `i.isLt : i.val < n` -- the proof that the number is in bounds

The field `.val` lets you extract the raw natural number from a `Fin n` element.
The field `.isLt` gives you the proof that this number is less than `n`.

## Your task

You are given `i : Fin 5`. Your goal is to prove that `i.val < 5`.

This is exactly the information stored in `i.isLt`. You can close this goal
with `exact i.isLt`.
"

/-- Every element of `Fin n` has a value strictly less than `n`. -/
Statement (i : Fin 5) : i.val < 5 := by
  Hint "The proof is already bundled inside `i`. Try `exact i.isLt`."
  exact i.isLt

Conclusion
"
The proof was already there -- `i.isLt` is precisely the statement `i.val < 5`.

This is the power of subtypes: when you have `i : Fin 5`, the bound `i.val < 5`
is not something you need to prove separately. It was proven when `i` was
constructed, and you can extract that proof whenever you need it.

**The coercion arrow `↑`**: In some contexts, Lean displays `i.val` as `↑i`
(with an up-arrow). This is an automatic coercion from `Fin n` to `Nat`.
The two notations mean exactly the same thing -- `↑i` is just `i.val`.
You will see both forms in goal states throughout this course.

In a paper proof, you would write: \"Since $i \\in \\{0, 1, \\ldots, 4\\}$,
we have $i < 5$.\" In Lean, `exact i.isLt` is the formal version of that
reasoning.
"

/-- `Fin.val` (also written `↑i` via coercion) extracts the underlying natural
number from a `Fin n` element. If `i : Fin n`, then `i.val : Nat`. -/
DefinitionDoc Fin.val as "Fin.val"

/-- `Fin.isLt` provides the proof that a `Fin n` element's value is less than `n`.
If `i : Fin n`, then `i.isLt : i.val < n`. This is the bound witness bundled
inside every `Fin` element. -/
DefinitionDoc Fin.isLt as "Fin.isLt"

NewDefinition Fin.val Fin.isLt
