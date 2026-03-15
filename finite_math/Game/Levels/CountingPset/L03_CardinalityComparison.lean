import GameServer.Commands
import Mathlib

World "CountingPset"
Level 3

Title "Subset implies cardinality inequality"

Introduction
"
# Subset → cardinality inequality

If every element of `s` is also in `t`, then `s` has at most as
many elements as `t`. This is the subset-card inequality:

```
Finset.card_le_card : s ⊆ t → s.card ≤ t.card
```

You proved this in the Finset Induction world. Now retrieve it on
fresh finsets.

## Your task

Given `h : s ⊆ t` where `s` and `t` are specific finsets of natural
numbers, prove `s.card ≤ t.card`.
"

/-- If `s ⊆ t`, then `s.card ≤ t.card`. -/
Statement (s t : Finset Nat) (h : s ⊆ t) : s.card ≤ t.card := by
  Hint (hidden := true) "Use `exact Finset.card_le_card h`."
  exact Finset.card_le_card h

Conclusion
"
You applied the subset-card inequality: from `s ⊆ t`, you derived
`s.card ≤ t.card` in a single step.

This is one of the most commonly used cardinality facts. In paper
mathematics, you would write: \"Since every element of $S$ is in $T$,
we have $|S| \\leq |T|$.\"

**Retrieval check**: This level retrieved the subset-cardinality
inequality (V15) on abstract finsets.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
