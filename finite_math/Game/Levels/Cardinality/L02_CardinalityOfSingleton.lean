import Game.Metadata

World "Cardinality"
Level 2

Title "Cardinality of a Singleton"

Introduction "
# One Element, One Count

A singleton set `{a}` contains exactly one element:

$$|\\{a\\}| = 1$$

In Lean: `Finset.card_singleton a : ({a} : Finset α).card = 1`

Notice that `card_singleton` takes the element `a` as an argument.
This is because different singletons are different finsets, so Lean
needs to know *which* singleton you're talking about.

**Your task**: Prove that `{7}` has exactly one element.
"

/-- A singleton finset has cardinality 1. -/
Statement : ({7} : Finset ℕ).card = 1 := by
  Hint "The goal matches `Finset.card_singleton 7`. Apply it directly."
  Hint (hidden := true) "Try `exact Finset.card_singleton 7`."
  exact Finset.card_singleton 7

Conclusion "
`Finset.card_singleton a` tells you that `{a}` has exactly one
element, regardless of what `a` is.

Together with `card_empty`, you now have the two base cases:
- $|\\emptyset| = 0$ (`card_empty`)
- $|\\{a\\}| = 1$ (`card_singleton a`)

The next level introduces the inductive step: what happens when you
`insert` a new element into a finset.
"

/-- `Finset.card_singleton a` states that `({a} : Finset α).card = 1`.

## Syntax
```
exact Finset.card_singleton a
rw [Finset.card_singleton]
```

## When to use it
When the goal involves the cardinality of a singleton finset `{a}`.
Note that `a` must be provided as an explicit argument.

## Example
```
-- Goal: ({5} : Finset ℕ).card = 1
exact Finset.card_singleton 5
```
-/
TheoremDoc Finset.card_singleton as "Finset.card_singleton" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_singleton

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
