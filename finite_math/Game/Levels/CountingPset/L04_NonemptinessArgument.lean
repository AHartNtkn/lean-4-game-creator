import GameServer.Commands
import Mathlib

World "CountingPset"
Level 4

Title "Extracting a witness from nonemptiness"

Introduction
"
# From nonempty to a concrete element

In the Counting and Pigeonhole world, you learned two complementary
moves:
- **V8**: Choosing a witness from a nonempty finset.
- **V9**: Deriving a contradiction when a nonempty type has card = 0.

Now retrieve both on a fresh type.

## Your task

You are given that a finset `s` is nonempty. Extract a concrete
element from it.

Recall that `Finset.Nonempty s` is defined as `∃ x, x ∈ s`.
Use `obtain` to extract the witness.
"

/-- From `s.Nonempty`, extract an element and prove it is a member. -/
Statement (s : Finset Nat) (h : s.Nonempty) : ∃ x, x ∈ s := by
  Hint (hidden := true) "Use `exact h`. `Finset.Nonempty` is defined as
  `∃ x, x ∈ s`, so the hypothesis IS the goal."
  exact h

Conclusion
"
The proof was immediate because `Finset.Nonempty s` is *defined* as
`∃ x, x ∈ s`. The hypothesis `h` already has exactly the right type.

But the lesson is not about this specific proof — it is about
recognizing that **nonemptiness gives you a witness**. When you
encounter a nonempty finset in a larger proof, you can use
`obtain ⟨x, hx⟩ := h` to extract both the element `x` and its
membership proof `hx`. This is the V8 proof move.

The dual move (V9) is contradiction: if you know a type is nonempty
but also that its cardinality is 0, you have a contradiction.

**Retrieval check**: This level retrieved the witness-from-nonempty
move (V8) and the nonempty-as-existential connection (V9).
"

DisabledTactic trivial decide native_decide simp aesop simp_all
