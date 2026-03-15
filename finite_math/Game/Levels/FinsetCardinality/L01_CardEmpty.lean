import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 1

Title "Cardinality of the empty finset"

Introduction
"
# Cardinality: counting elements systematically

Welcome to the **Cardinality** world. You have already seen `Finset.card`
in passing — you used `card_singleton` and `card_insert_of_notMem` to
compute the size of literal finsets. Now we study cardinality as a
systematic topic.

## The key question

Given a finset `s`, what is `s.card`? This world answers that question
for progressively more complex finsets, culminating in the
**inclusion-exclusion principle**.

## `Finset.card_empty`

The simplest cardinality fact is:

```
Finset.card_empty : (∅ : Finset α).card = 0
```

The empty finset has zero elements. This is the base case for all
cardinality reasoning — analogous to how `∅` is the base case for
finset construction.

## Your task

Prove that `(∅ : Finset Nat).card = 0` using `Finset.card_empty`.
"

/-- The empty finset has cardinality 0. -/
Statement : (∅ : Finset Nat).card = 0 := by
  Hint "The goal is `(∅ : Finset Nat).card = 0`. What lemma directly
  states this fact?"
  Hint (hidden := true) "Use `rw [Finset.card_empty]` or
  `exact Finset.card_empty`."
  rw [Finset.card_empty]

Conclusion
"
You proved the base case of cardinality: the empty finset has zero elements.

The lemma `Finset.card_empty` is the cardinality analogue of `Finset.empty` —
it is the starting point for all cardinality computations.

## The cardinality hierarchy

You now know three cardinality lemmas:
- `Finset.card_empty : (∅).card = 0` — base case (this level)
- `Finset.card_singleton : ({a}).card = 1` — from W5
- `Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1` — from W5

Together, these three lemmas let you compute the cardinality of any finset
built by iterated `insert`. This world will add more tools to the kit.

**In plain language**: \"The empty set has no elements, so its cardinality
is zero. This is the base case for counting.\"
"

/-- `Finset.card_empty` states that `(∅ : Finset α).card = 0`.

The empty finset has zero elements. This is the base case for
cardinality computations. -/
TheoremDoc Finset.card_empty as "Finset.card_empty" in "Finset"

NewTheorem Finset.card_empty
DisabledTactic trivial decide native_decide aesop simp_all
