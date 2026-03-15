import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 3

Title "A set-operation identity"

Introduction
"
# A fresh set-operation identity

Prove the **absorption law** for finsets:

```
s ∩ (s ∪ t) = s
```

This says: intersecting `s` with `s ∪ t` just gives back `s`,
because every element of `s` is in `s ∪ t`, and every element
of `s ∩ (s ∪ t)` is in `s`.

## Strategy

Use `ext a` to reduce to membership, then split the biconditional
and use `mem_inter`, `mem_union`, and basic logic.
"

/-- The absorption law: `s ∩ (s ∪ t) = s`. -/
Statement (s t : Finset Nat) : s ∩ (s ∪ t) = s := by
  Hint (hidden := true) "Use `ext a` to reduce to a membership
  biconditional."
  ext a
  Hint (hidden := true) "Use `constructor` to split the iff."
  constructor
  · Hint (hidden := true) "Use `intro h`, then
    `rw [Finset.mem_inter] at h` and extract the first component."
    intro h
    rw [Finset.mem_inter] at h
    exact h.1
  · Hint (hidden := true) "Use `intro ha`, then
    `rw [Finset.mem_inter]`, `constructor`, `exact ha`, then
    `rw [Finset.mem_union]`, `left`, `exact ha`."
    intro ha
    rw [Finset.mem_inter]
    constructor
    · exact ha
    · rw [Finset.mem_union]
      left
      exact ha

Conclusion
"
You proved the absorption law `s ∩ (s ∪ t) = s`. This is a standard
identity in lattice theory, and the proof uses the same `ext` +
membership-rewriting technique you learned in W7.

**Retrieval check**: This level retrieved `ext` for finset equality
(V6) and case analysis on membership (V7) on a fresh identity.
"

DisabledTactic trivial decide native_decide aesop simp_all
