import GameServer.Commands
import Mathlib

World "FinCompute"
Level 2

Title "The semicolon combinator"

Introduction
"
# The `<;>` Combinator

Writing `omega` three times (or four, or five) after `fin_cases` gets
tedious. Lean provides a shorthand: the **semicolon combinator** `<;>`.

## How `<;>` works

`tactic₁ <;> tactic₂` means: \"run `tactic₁`, then apply `tactic₂`
to **every** goal that `tactic₁` produced.\"

So `fin_cases i <;> omega` means:
1. `fin_cases i` --- split into one goal per element
2. `omega` --- try to close each goal

If `omega` succeeds on every case, the whole proof is done in one line.

**The `<;>` combinator is general.** It works with any pair of tactics,
not just `fin_cases` and `omega`. You will see patterns like
`constructor <;> intro h` or `ext <;> simp` in later worlds.

## Your task

Prove that for every `i : Fin 4`, the value `3 * i.val + 2 < 15`.

Use `intro i` and then `fin_cases i <;> omega` to close all four cases
in one line.
"

/-- For every element of `Fin 4`, three times its value plus two is less than 15. -/
Statement : ∀ i : Fin 4, 3 * i.val + 2 < 15 := by
  Hint "Start with `intro i` to introduce the variable."
  intro i
  Hint "Use `fin_cases i <;> omega` to split into four cases and close them all."
  Hint (hidden := true) "The `<;>` combinator applies `omega` to every goal produced
  by `fin_cases i`. Since all four arithmetic inequalities are within `omega`'s scope,
  the whole proof closes in one line."
  fin_cases i <;> omega

Conclusion
"
The `fin_cases i <;> omega` combination is a workhorse pattern for `Fin n`
arithmetic. It works whenever:
- `n` is a specific number (not a variable),
- the property involves arithmetic that `omega` can verify.

Note how this is different from the W1 boss approach, where we used
`have hi := i.isLt` and then `omega`. That approach works for *any* `n`,
because `omega` can reason about the inequality `i.val < n` abstractly.
The `fin_cases` approach works only for *specific* small `n`, but it is
more powerful: it can verify properties that don't follow from `i.val < n`
alone.

**Remember**: `<;>` is not specific to `fin_cases` or `omega`. It is a
general tactic combinator that applies the right-hand tactic to every
goal the left-hand tactic creates. Think of it as \"do this to all
remaining goals.\"

**When to use which strategy:**
- `i.isLt` + `omega`: for properties that follow from the bound alone
- `fin_cases` + `omega`: for properties that need each case checked individually
"

DisabledTactic decide native_decide
