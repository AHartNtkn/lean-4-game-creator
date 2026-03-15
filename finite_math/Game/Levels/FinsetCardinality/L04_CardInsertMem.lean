import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 4

Title "Inserting a duplicate: no change"

Introduction
"
# What if the element is already there?

In Level 3, you proved that inserting a **new** element increases the
cardinality by 1. But what if the element is already in the finset?

## `Finset.card_insert_of_mem`

```
Finset.card_insert_of_mem : a ∈ s → (insert a s).card = s.card
```

If `a` is already in `s`, then `insert a s = s` (because finsets have
no duplicates), so the cardinality does not change.

This is the cardinality consequence of the misconception you saw earlier:
`insert a s` is a **no-op** when `a ∈ s`.

## Your task

Given `h : a ∈ s`, prove that `(insert a s).card = s.card`.
"

/-- Inserting a duplicate does not change cardinality. -/
Statement {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (h : a ∈ s) : (insert a s).card = s.card := by
  Hint "You have `h : a ∈ s`. What lemma connects membership to the
  cardinality of `insert a s`?"
  Hint (hidden := true) "Use `rw [Finset.card_insert_of_mem h]` or
  `exact Finset.card_insert_of_mem h`."
  exact Finset.card_insert_of_mem h

Conclusion
"
Good. This is the **contrast case** to Level 3: when `a ∈ s`, inserting
`a` does nothing to the cardinality.

## The two insertion lemmas

| Condition | Lemma | Result |
|-----------|-------|--------|
| `a ∉ s` | `card_insert_of_notMem` | `(insert a s).card = s.card + 1` |
| `a ∈ s` | `card_insert_of_mem` | `(insert a s).card = s.card` |

In ordinary math, this dichotomy is obvious: you either add a new element
or you do not. In Lean, you must decide which case applies and provide the
appropriate proof.

**In plain language**: \"Adding a duplicate to a set does not change its size.\"
"

/-- `Finset.card_insert_of_mem` states that if `a ∈ s`, then
`(insert a s).card = s.card`.

Inserting a duplicate does not change the cardinality. -/
TheoremDoc Finset.card_insert_of_mem as "Finset.card_insert_of_mem" in "Finset"

NewTheorem Finset.card_insert_of_mem
DisabledTactic trivial decide native_decide aesop simp_all
