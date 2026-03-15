import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 3

Title "Cardinality after inserting a new element"

Introduction
"
# The insertion lemma revisited

You used `Finset.card_insert_of_notMem` in the Constructing Finsets world
to peel apart literal finsets. Now we use it in a slightly more abstract
setting: proving a cardinality equation about a generic finset `s`.

## Recall

```
Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1
```

If `a` is genuinely new (not already in `s`), then inserting it increases
the cardinality by exactly 1.

## Your task

Given a finset `s` and an element `a` with `a ∉ s`, prove that
`(insert a s).card = s.card + 1`.

This is just a direct application of the lemma, but the goal is to
practice using the non-membership hypothesis `h`.
"

/-- Inserting a new element increases cardinality by 1. -/
Statement {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (h : a ∉ s) : (insert a s).card = s.card + 1 := by
  Hint "You have `h : a ∉ s` and need to show the cardinality
  equation. What lemma takes a non-membership proof and produces
  a cardinality equation for `insert`?"
  Hint (hidden := true) "Use `rw [Finset.card_insert_of_notMem h]`
  or `exact Finset.card_insert_of_notMem h`."
  exact Finset.card_insert_of_notMem h

Conclusion
"
You applied `card_insert_of_notMem` directly. In the previous world,
you used it concretely (with specific numbers). Here, you used it
abstractly (with a generic finset and element).

## The pattern

The proof pattern for computing cardinalities of literal finsets is:
1. Peel off each `insert` using `card_insert_of_notMem`.
2. Handle the innermost singleton with `card_singleton`.
3. Let arithmetic close the remaining goal.

This pattern will appear again in the boss level.

**In plain language**: \"If an element is not already in a set, adding
it increases the count by 1.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
