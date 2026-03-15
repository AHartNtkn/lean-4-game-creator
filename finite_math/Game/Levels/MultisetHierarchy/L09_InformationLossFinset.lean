import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 9

Title "Information loss: different lists, same finset"

Introduction
"
# Even more information loss

In Level 4, you saw that different lists can give the **same multiset**
(because multisets forget order). Now you will see a more dramatic kind
of information loss: different lists can give the **same finset**, even
when they have different lengths and different multisets.

## `List.toFinset`

`List.toFinset` is a shortcut that goes directly from `List` to `Finset`,
combining both steps of the hierarchy (forget order, then forget
multiplicity) in one operation.

Consider these two lists:
- `[1, 2, 3]` -- three elements, no duplicates
- `[3, 2, 1, 2]` -- four elements, with `2` appearing twice

Both produce the finset `{1, 2, 3}`.

## Your task

Prove that the lists `[1, 2, 3]` and `[3, 2, 1, 2]` produce the same
finset when converted with `List.toFinset`.
"

/-- Two different lists can produce the same finset. -/
Statement : ([1, 2, 3] : List Nat).toFinset = ([3, 2, 1, 2] : List Nat).toFinset := by
  Hint "Both sides evaluate to the same finset. This is a concrete decidable
  equality. What tactic can verify it?"
  Hint (hidden := true) "Try `decide`. It evaluates both `toFinset` calls and
  compares the results."
  decide

Conclusion
"
The lists `[1, 2, 3]` (3 elements) and `[3, 2, 1, 2]` (4 elements) are
very different -- different lengths, different orderings, different
multiplicities -- but they produce the same finset `{1, 2, 3}`.

Compare the two kinds of information loss you have seen:

| Conversion | What is lost | Level 4 example | This level |
|-----------|-------------|----------------|------------|
| List → Multiset | Order | `[1,2,3]` and `[3,1,2]` give same multiset | -- |
| List → Finset | Order + multiplicity | -- | `[1,2,3]` and `[3,2,1,2]` give same finset |

The finset conversion is \"more lossy\" than the multiset conversion: it
forgets both order **and** multiplicity. The lists `[1, 2, 3]` and `[3, 2, 1, 2]`
have the same finset but **different** multisets (because one has two copies
of `2`).

This demonstrates that `List.toFinset` is **not injective**: different inputs
can produce the same output.

**In plain language**: \"The set of elements in a sequence does not tell
you the sequence -- you lose the order and the repeats.\"
"

/-- `List.toFinset l` converts list `l` directly to a finset, combining both
steps of the hierarchy: forgetting order and removing duplicates.

It is equivalent to `Multiset.toFinset (↑l)` -- first coerce to multiset,
then convert to finset. -/
DefinitionDoc List.toFinset as "List.toFinset"

NewDefinition List.toFinset
DisabledTactic trivial native_decide simp aesop simp_all
