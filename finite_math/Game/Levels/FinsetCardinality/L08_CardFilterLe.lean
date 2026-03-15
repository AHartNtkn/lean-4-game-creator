import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 8

Title "Filtering cannot increase cardinality"

Introduction
"
# Cardinality of a filtered finset

When you filter a finset by a predicate, you can only keep or remove
elements — never add new ones. So the filtered finset is never larger
than the original.

## `Finset.card_filter_le`

```
Finset.card_filter_le :
  (s.filter p).card ≤ s.card
```

This says: filtering can only decrease (or maintain) the cardinality.

## Why this matters

This inequality is a fundamental monotonicity fact. It says that
selecting a subset (by a predicate) cannot produce more elements
than you started with. You will use this kind of reasoning when
proving bounds on counts.

## Your task

Prove the inequality for a specific case: filtering the even numbers
from `{1, 2, 3, 4, 5}` produces at most 5 elements.
"

/-- Filtering the evens from {1,2,3,4,5} gives at most 5 elements. -/
Statement : (Finset.filter (fun x => x % 2 = 0)
    ({1, 2, 3, 4, 5} : Finset Nat)).card ≤
    ({1, 2, 3, 4, 5} : Finset Nat).card := by
  Hint "The goal is `(s.filter p).card ≤ s.card`. What lemma gives
  this inequality directly?"
  Hint (hidden := true) "Use `exact Finset.card_filter_le _ _`."
  exact Finset.card_filter_le _ _

Conclusion
"
You proved that filtering cannot increase cardinality. The lemma
`Finset.card_filter_le` handles this in full generality — it works
for any predicate and any finset.

## Intuition

Filtering selects a subset. A subset cannot have more elements than
the original set. This is the cardinality analogue of `filter_subset`:

- `Finset.filter_subset : s.filter p ⊆ s` (subset relation)
- `Finset.card_filter_le : (s.filter p).card ≤ s.card` (cardinality consequence)

The inequality is a consequence of the subset relation, but
`card_filter_le` is stated directly for convenience.

**In plain language**: \"Selecting elements that satisfy a property
from a set cannot produce more elements than the original set.\"
"

/-- `Finset.card_filter_le` states that
`(s.filter p).card ≤ s.card`.

Filtering a finset by a predicate can only decrease or maintain
the cardinality. -/
TheoremDoc Finset.card_filter_le as "Finset.card_filter_le" in "Finset"

NewTheorem Finset.card_filter_le
DisabledTactic trivial decide native_decide aesop simp_all
