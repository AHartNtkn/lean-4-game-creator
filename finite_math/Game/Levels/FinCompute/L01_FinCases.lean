import GameServer.Commands
import Mathlib

World "FinCompute"
Level 1

Title "Introducing fin_cases"

Introduction
"
# Exhaustive Case Analysis on `Fin n`

In the previous world, you proved properties of `Fin n` elements using
`intro` and `omega`. But there is a much more direct approach for *small*
`Fin n`: simply check every possible value.

## The `fin_cases` tactic

When you have a hypothesis `i : Fin n` (for a concrete `n`), the tactic
`fin_cases i` replaces the single goal with `n` separate goals --- one
for each possible value of `i`.

For example, if `i : Fin 3`, then `fin_cases i` produces three goals
where `i` is replaced by `0`, `1`, and `2` respectively.

This is the **exhaustive verification** pattern: you verify the claim for
every element individually, and since `Fin n` has exactly `n` elements,
that covers everything.

## Your task

Prove that every element of `Fin 3` satisfies `i.val < 10`.

After `intro i` and `fin_cases i`, you will have three goals.
Each one is a concrete arithmetic statement that `omega` can handle.
You can close each goal separately with `omega`, or handle all three
at once --- we will learn how in the next level.
"

/-- Every element of `Fin 3` has value less than 10. -/
Statement : ∀ i : Fin 3, i.val < 10 := by
  Hint "Start with `intro i` to introduce the variable."
  intro i
  Hint "Now use `fin_cases i` to split into cases for each element of `Fin 3`."
  Hint (hidden := true) "After `fin_cases i`, you will have three separate goals.
  Close each one with `omega`."
  fin_cases i
  · omega
  · omega
  · omega

/-- `fin_cases h` performs exhaustive case analysis on a hypothesis
`h : Fin n` (for a concrete numeral `n`). It replaces the current goal
with `n` separate goals, one for each possible value.

**Example**: If `i : Fin 3`, then `fin_cases i` produces goals for
`i = 0`, `i = 1`, and `i = 2`.

**When to use**: When you want to verify a property by checking every
element of a small finite type individually. For large `n`, use
`i.isLt` + `omega` instead. -/
TacticDoc fin_cases

Conclusion
"
The `fin_cases` tactic examined all three possibilities:
- When `i = 0`: `0 < 10` ✓
- When `i = 1`: `1 < 10` ✓
- When `i = 2`: `2 < 10` ✓

Since every case holds, the universal statement is proved.

We call this proof pattern **exhaustive verification** (or *proof by
exhaustion*): enumerate every element, check the property for each one.
It works whenever `Fin n` is small enough that checking every case is
practical. For large `n`, you would need a different approach (like
`omega` with `i.isLt`), but for small concrete types, exhaustion is
clean and direct.

**In plain language**: \"There are exactly three elements in $\\{0, 1, 2\\}$.
We check each one: $0 < 10$, $1 < 10$, $2 < 10$. Done.\"
"

NewTactic fin_cases
DisabledTactic decide native_decide
