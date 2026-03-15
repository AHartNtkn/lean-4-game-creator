import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 2

Title "Cardinality of a singleton"

Introduction
"
# Retrieving `card_singleton`

You already know `Finset.card_singleton` from the Constructing Finsets
world. This level is a **retrieval exercise**: can you still reach for
the right lemma when the context is different?

## Recall

```
Finset.card_singleton a : ({a} : Finset α).card = 1
```

A singleton finset has exactly one element.

## Your task

Prove that `({42} : Finset Nat).card = 1`. The specific number does
not matter — `card_singleton` works for any `a`.
"

/-- The singleton {42} has cardinality 1. -/
Statement : ({42} : Finset Nat).card = 1 := by
  Hint "The goal involves the cardinality of a singleton finset.
  What lemma gives the cardinality of a singleton?"
  Hint (hidden := true) "Use `rw [Finset.card_singleton]`."
  rw [Finset.card_singleton]

Conclusion
"
Good — you retrieved `Finset.card_singleton` in a new context. The
specific element `42` did not matter; the lemma is polymorphic in `a`.

## Building blocks so far

| Finset | Cardinality | Lemma |
|--------|-------------|-------|
| `∅` | 0 | `card_empty` |
| `{a}` | 1 | `card_singleton` |
| `insert a s` (if `a ∉ s`) | `s.card + 1` | `card_insert_of_notMem` |

These three handle any finset built from iterated `insert`. Next, we
will use them together.

**In plain language**: \"A set with one element has cardinality 1.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
