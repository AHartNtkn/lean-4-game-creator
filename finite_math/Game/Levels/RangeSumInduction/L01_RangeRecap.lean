import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 1

Title "Range recap"

Introduction
"
# Induction on range sums

Welcome to the **Range Sum Induction** world! In this world you will
learn to prove identities about sums of the form
$$\\sum_{i=0}^{n-1} f(i)$$
by induction on $n$, using the key lemma `sum_range_succ` to peel off
the last term.

## Review: `Finset.range`

Recall that `Finset.range n` is the finset `{0, 1, …, n-1}`. The
critical facts are:

- **`Finset.range_zero`**: `range 0 = ∅`
- **`Finset.mem_range`**: `k ∈ range n ↔ k < n`
- **`Finset.card_range`**: `(range n).card = n`

These will reappear throughout the world.

## Your task

Prove that `(Finset.range 5).card = 5`.

This is a direct application of `Finset.card_range`.
"

/-- The cardinality of `range 5` is `5`. -/
Statement : (Finset.range 5).card = 5 := by
  Hint "Use `norm_num [Finset.card_range]` to compute the cardinality.
  Or use `rw [Finset.card_range]` followed by `rfl`."
  Hint (hidden := true) "Try `rw [Finset.card_range]`."
  rw [Finset.card_range]

Conclusion
"
You verified that `range 5` has exactly 5 elements. The lemma
`Finset.card_range` states this in general:

```
Finset.card_range (n : Nat) : (Finset.range n).card = n
```

## What comes next

Sums over `range n` will be our main object of study. The key technique
is *induction on n*, peeling off the last term of the sum at each step.
The next level introduces the lemma that makes this work:
`Finset.sum_range_succ`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
