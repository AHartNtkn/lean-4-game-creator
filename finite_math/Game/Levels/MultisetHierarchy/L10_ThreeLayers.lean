import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 10

Title "The three-layer hierarchy"

Introduction
"
# Comparing cardinalities across the hierarchy

Let us now see all three layers side by side on the same data.

Consider the list `l = [1, 2, 1, 3]`:
- As a **list**: `l.length = 4` (four elements, including the duplicate `1`)
- As a **multiset**: `(↑l).card = 4` (same count -- multisets keep duplicates)
- As a **finset**: `(↑l).toFinset.card = 3` (only three **distinct** elements)

The cardinality can **decrease** when moving from multiset to finset (because
duplicates are removed), but it **never increases**.

## `Finset.card`

`Finset.card s` returns the number of elements in a finset `s`. Since a
finset has no duplicates, this is the number of **distinct** elements.

## Your task

Prove that for the list `[1, 2, 1, 3]`:
1. The multiset cardinality equals the list length (both are 4), **and**
2. The finset cardinality is 3.

Use `constructor` to split the conjunction, then handle each part.
"

/-- The list `[1, 2, 1, 3]` has multiset cardinality 4 and finset cardinality 3. -/
Statement : Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) = 4 ∧
    (↑([1, 2, 1, 3] : List Nat) : Multiset Nat).toFinset.card = 3 := by
  Hint "The goal is a conjunction (`∧`). What tactic splits a conjunction into
  two separate goals?"
  Hint (hidden := true) "Use `constructor` to split the conjunction into two parts."
  constructor
  · Hint "The multiset cardinality of a coerced list is definitionally equal to
    the list's length. Since `[1, 2, 1, 3].length = 4`, this holds by definition.
    What tactic proves definitional equalities?"
    Hint (hidden := true) "Try `rfl`."
    rfl
  · Hint "The finset cardinality requires computing `toFinset` first (which removes
    the duplicate `1`), then counting. This is a concrete computation. Try `decide`."
    decide

Conclusion
"
Here is the key comparison:

```
List    [1, 2, 1, 3]     length = 4     (order + duplicates)
           ↓ ↑
Multiset {1, 2, 1, 3}    card = 4       (duplicates, no order)
           ↓ toFinset
Finset   {1, 2, 3}       card = 3       (no duplicates, no order)
```

The multiset cardinality equals the list length because coercion preserves
multiplicity -- it only forgets order. But the finset cardinality is smaller
because `toFinset` removes the duplicate `1`.

**General fact**: For any list `l`,
`(↑l).toFinset.card ≤ (↑l).card = l.length`

Equality holds exactly when the list has no duplicates. You will prove a
version of this inequality in the next level.

**In plain language**: \"A bag has the same number of items as the list it
came from (just scrambled). A set may have fewer items because it drops
the repeats.\"
"

/-- `Finset.card s` returns the number of elements in finset `s`. Since a finset
contains no duplicates, this is the number of **distinct** elements.

For example, if `s = {1, 2, 3}`, then `Finset.card s = 3`. -/
DefinitionDoc Finset.card as "Finset.card"

NewDefinition Finset.card
DisabledTactic trivial decide native_decide simp aesop simp_all
