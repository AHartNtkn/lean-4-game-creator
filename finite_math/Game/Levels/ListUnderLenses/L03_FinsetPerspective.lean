import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 3

Title "As a Finset"

Introduction
"
# The finset lens

Now the third lens: **finsets**. A finset forgets both order **and**
multiplicity, keeping only the **distinct** elements.

Recall from the Multisets and Hierarchy world:
- `Multiset.toFinset` converts a multiset to a finset by removing duplicates.
- `Finset.card` counts the number of **distinct** elements.

## What changes this time?

When we convert the multiset `↑[1, 2, 1, 3]` to a finset:
- The duplicate `1` is removed.
- The resulting finset is `{1, 2, 3}`.
- The cardinality drops from 4 to **3**.

This is the crucial difference: **the finset has fewer elements** than
the list or multiset, because the repeated `1` is counted only once.

## Your task

Prove two facts about `[1, 2, 1, 3]` viewed through the finset lens:
1. Converting to a finset gives `{1, 2, 3}`.
2. The finset has cardinality 3.

Both are concrete computations that `decide` can handle.
"

/-- Converting `↑[1, 2, 1, 3]` to a finset gives `{1, 2, 3}`, which has 3 elements. -/
Statement : Multiset.toFinset (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = {1, 2, 3} ∧
    (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset.card = 3 := by
  Hint "Use `constructor` to split the conjunction."
  constructor
  · Hint "The first goal asks whether `toFinset` of a concrete multiset
    equals a concrete finset. Both sides can be evaluated. What tactic
    evaluates decidable equalities on concrete data?"
    Hint (hidden := true) "Try `decide`. It evaluates `toFinset` on the
    concrete multiset and compares with the expected finset."
    decide
  · Hint "The second goal asks for the cardinality of the resulting finset.
    After deduplication, the finset has 3 elements (the distinct values
    1, 2, and 3). This is a concrete computation."
    Hint (hidden := true) "Try `decide`."
    decide

Conclusion
"
Here is the full three-layer comparison:

```
List     [1, 2, 1, 3]     length = 4     (order + duplicates)
            ↓ ↑
Multiset {1, 2, 1, 3}     card = 4       (duplicates, no order)
            ↓ toFinset
Finset   {1, 2, 3}         card = 3       (no duplicates, no order)
```

The finset `{1, 2, 3}` has **three** elements, not four. The duplicate `1`
was removed by `toFinset`. This is information loss: given only the finset
`{1, 2, 3}`, you cannot tell that `1` originally appeared twice.

**Key insight**: The same data produces different cardinalities depending
on which mathematical lens you use:
- **List**: 4 (counts order and duplicates)
- **Multiset**: 4 (counts duplicates, forgets order)
- **Finset**: 3 (forgets both duplicates and order)

**In plain language**: \"The set of distinct elements in 1, 2, 1, 3 is
{1, 2, 3}, which has 3 elements. The repeated 1 does not add to the set.\"
"

DisabledTactic trivial native_decide simp aesop simp_all
