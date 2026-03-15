import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 4

Title "Filtering a sum"

Introduction
"
## Level 4: `sum_filter` on a new predicate

In W16, you used `sum_filter` with the predicate `Even`. Now use it
with a different predicate.

Prove that summing cubes over the elements of `range n` that are
less than `5` equals summing `if i < 5 then i ^ 3 else 0` over
all of `range n`.

This is a direct application of `Finset.sum_filter`.
"

/-- Filtering a sum with a new predicate. -/
Statement (n : Nat) :
    ∑ i ∈ (Finset.range n).filter (· < 5), i ^ 3 =
    ∑ i ∈ Finset.range n, if i < 5 then i ^ 3 else 0 := by
  Hint (hidden := true) "Use `rw [Finset.sum_filter]` to convert the
  filtered sum into a conditional sum."
  rw [Finset.sum_filter]

Conclusion
"
You applied `sum_filter` to a new predicate (`· < 5` instead of
`Even`). The lemma works identically regardless of the predicate:

```
∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0
```

**Retrieval check**: You retrieved M38 (`sum_filter` / conditional
splitting) on a fresh surface form.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
