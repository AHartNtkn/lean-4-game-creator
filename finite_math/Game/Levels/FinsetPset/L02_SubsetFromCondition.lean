import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 2

Title "Subset from a condition"

Introduction
"
# Subset from a condition

Prove that `{5, 10} ⊆ {5, 10, 15, 20}`.

Recall: `s ⊆ t` unfolds to `∀ a, a ∈ s → a ∈ t`. So you introduce
an element `a` and its membership hypothesis `ha : a ∈ s`, then show
`a ∈ t`.

There is no new material here. This is the subset proof pattern from
W7 on a fresh pair of finsets.
"

/-- `{5, 10}` is a subset of `{5, 10, 15, 20}`. -/
Statement : ({5, 10} : Finset Nat) ⊆ {5, 10, 15, 20} := by
  Hint (hidden := true) "Start with `intro a ha`, then use
  `simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢`
  and handle the cases."
  intro a ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha ⊢
  rcases ha with rfl | rfl <;> simp

Conclusion
"
You proved a subset relation on a new pair of finsets. The proof
pattern is always the same:

1. Introduce an element and its membership in the smaller finset.
2. Show it belongs to the larger finset.

The specifics of *which* elements are involved do not change the
proof structure.

**Retrieval check**: This level retrieved the subset proof move (V14)
on a fresh surface.
"

DisabledTactic trivial decide native_decide aesop simp_all
