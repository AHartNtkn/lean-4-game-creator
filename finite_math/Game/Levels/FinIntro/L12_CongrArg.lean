import GameServer.Commands
import Mathlib

World "FinIntro"
Level 12

Title "Extracting value-level consequences"

Introduction
"
# `congr_arg` -- applying a function to both sides of an equality

You know that two `Fin n` elements are equal if and only if their values
are equal (`Fin.ext_iff`). You have used the `ext` tactic to go from
`a = b` at the `Fin` level to `a.val = b.val` at the `Nat` level.

But sometimes you need to go in the other direction of reasoning: if you
*already know* that `a = b` as `Fin` elements, you can *extract* that
`a.val = b.val`. The tool for this is `congr_arg`.

`congr_arg` takes a function `f` and a proof `h : a = b`, and produces
`congr_arg f h : f a = f b`. In other words: if `a = b`, then `f a = f b`
for any function `f`.

For `Fin`, the function `Fin.val` extracts the value. So:
```
congr_arg Fin.val h : a.val = b.val
```

whenever `h : a = b` for `a b : Fin n`.

## Your task

Given `a b : Fin 3` and `h : a = b`, prove that `a.val = b.val`.

Use `exact congr_arg Fin.val h`.
"

/-- If two `Fin` elements are equal, their values are equal. -/
Statement (a b : Fin 3) (h : a = b) : a.val = b.val := by
  Hint "Apply `Fin.val` to both sides of `h` using `congr_arg`.
  Try `exact congr_arg Fin.val h`."
  exact congr_arg Fin.val h

Conclusion
"
`congr_arg` is a fundamental tool: from `h : a = b`, you can derive
`congr_arg f h : f a = f b` for *any* function `f`. Here you used
`f = Fin.val` to extract a value-level equality from a `Fin`-level
equality.

This is the converse of what `ext` does:
- `ext` goes from \"values equal\" to \"Fin elements equal\"
- `congr_arg Fin.val` goes from \"Fin elements equal\" to \"values equal\"

You will use this pattern in the boss level: given a hypothesis that two
`Fin` elements are equal, `congr_arg Fin.val` extracts the numerical
consequence, which you can then use for arithmetic reasoning with `omega`.

**In paper proofs**: this step corresponds to \"If $a = b$ as elements
of $\\text{Fin}\\, n$, then in particular their underlying values are equal.\"
This is so obvious on paper that mathematicians rarely state it explicitly --
but in Lean, `congr_arg` makes it formal.
"

/-- `congr_arg f h` produces `f a = f b` from `h : a = b`. It applies a function
to both sides of an equality. For example, `congr_arg Fin.val h` extracts
`a.val = b.val` from `h : a = b` for `a b : Fin n`. -/
TheoremDoc congr_arg as "congr_arg" in "Logic"

NewTheorem congr_arg
