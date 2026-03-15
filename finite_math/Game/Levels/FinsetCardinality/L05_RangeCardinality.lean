import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 5

Title "Range and its cardinality"

Introduction
"
# `Finset.range` revisited

You first saw `Finset.range` in the Finset Exploration world, where you
used it to build `{1, 2, 3, 4, 5}` via `Finset.image (· + 1) (Finset.range 5)`.
Now we study its cardinality.

## Recall

`Finset.range n` is the finset `{0, 1, 2, ..., n-1}` — the natural
numbers strictly less than `n`. It contains exactly `n` elements.

## `Finset.card_range`

```
Finset.card_range : (Finset.range n).card = n
```

The cardinality of `range n` is `n`. This is a clean, memorable fact:
the range of `n` has `n` elements.

## `Finset.mem_range`

To reason about membership:

```
Finset.mem_range : m ∈ Finset.range n ↔ m < n
```

## Your task

Prove that `(Finset.range 5).card = 5`.
"

/-- The range of 5 has 5 elements. -/
Statement : (Finset.range 5).card = 5 := by
  Hint "The goal is `(Finset.range 5).card = 5`. What lemma gives the
  cardinality of `Finset.range n`?"
  Hint (hidden := true) "Use `rw [Finset.card_range]`."
  rw [Finset.card_range]

Conclusion
"
You proved that `range 5` has 5 elements. The lemma `Finset.card_range`
is clean and general: `(range n).card = n` for any `n`.

## Why `Finset.range` matters

`Finset.range n` is the standard index set for big operators. When you
write `∑ i in Finset.range n, f i` later in this course, you are
summing `f 0 + f 1 + ... + f (n-1)`. Understanding its cardinality is
foundational.

## Warning: 0-indexed!

`Finset.range 5 = {0, 1, 2, 3, 4}` — **not** `{1, 2, 3, 4, 5}`.
The largest element is `n - 1`, not `n`. This is consistent with
`Fin n`, which also ranges from `0` to `n - 1`.

**In plain language**: \"The set {0, 1, ..., n-1} has n elements.\"
"

/-- `Finset.card_range` states that `(Finset.range n).card = n`.

The range of `n` contains exactly `n` elements: `0, 1, ..., n-1`. -/
TheoremDoc Finset.card_range as "Finset.card_range" in "Finset"

NewTheorem Finset.card_range
DisabledTactic trivial decide native_decide aesop simp_all
