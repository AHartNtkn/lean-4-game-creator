import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 3

Title "Cardinality of Option types"

Introduction
"
# Option types add one element

The type `Option α` contains all elements of `α` (wrapped as `some a`)
plus one additional element `none`. Its cardinality is therefore:
```
Fintype.card_option : Fintype.card (Option α) = Fintype.card α + 1
```

This is useful when you need a type with \"one more element\" than
another --- a pattern that appears naturally in pigeonhole arguments.

## Your task

Prove that `Option (Fin 3)` has exactly 4 elements.

The elements are: `some 0`, `some 1`, `some 2`, and `none`.
"

/-- `Option (Fin 3)` has exactly 4 elements. -/
Statement : Fintype.card (Option (Fin 3)) = 4 := by
  Hint "Use `rw [Fintype.card_option]` to split the cardinality into
  `Fintype.card (Fin 3) + 1`."
  rw [Fintype.card_option]
  Hint "Now use `rw [Fintype.card_fin]` to evaluate `Fintype.card (Fin 3) = 3`.
  The remaining goal `3 + 1 = 4` is handled by Lean."
  Hint (hidden := true) "Use `rw [Fintype.card_fin]`."
  rw [Fintype.card_fin]

Conclusion
"
The proof followed the same pattern as the previous levels:

1. `Fintype.card_option` decomposed: `|\\text{Option (Fin 3)}| =
   |\\text{Fin 3}| + 1`.
2. `Fintype.card_fin` evaluated: `3 + 1 = 4`.

## Why Option matters

The `Option` type is Lean's way of adding a \"missing\" or \"null\" value.
For finite types, it increases the cardinality by exactly one.

This will be important for the pigeonhole principle: when we have
$n + 1$ objects to place into $n$ boxes, the domain has one more element
than the codomain --- exactly the relationship between `Option (Fin n)`
and `Fin n`.

**In plain language**: \"The set $\\{0, 1, 2, \\text{none}\\}$ has $3 + 1 = 4$
elements.\"
"

/-- `Fintype.card_option` states that `Option α` has one more element than `α`:
```
Fintype.card_option : Fintype.card (Option α) = Fintype.card α + 1
```

**When to use**: When computing the cardinality of `Option α`, or when
you need to express that a type has \"one more element\" than another. -/
TheoremDoc Fintype.card_option as "Fintype.card_option" in "Fintype"

NewTheorem Fintype.card_option
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
