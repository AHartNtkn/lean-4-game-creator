import GameServer.Commands
import Mathlib

World "FinsetPset"
Level 1

Title "Fresh membership goal"

Introduction
"
# Finset Reasoning: Problem Set

Welcome to the first problem set for finset reasoning. In this world
you will retrieve skills from the previous five worlds under
**reduced scaffolding**: fewer hints, fresh surface forms, and new
contexts.

## Level 1: Membership in a fresh context

You have proved membership facts for finsets like `{1, 2, 3}`.
Now work with a different finset: `{10, 20, 30, 40}`.

Prove that `30` belongs to this finset.

Recall the key lemma:
```
Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s
```
"

/-- `30` belongs to the finset `{10, 20, 30, 40}`. -/
Statement : (30 : Nat) ∈ ({10, 20, 30, 40} : Finset Nat) := by
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You proved membership in a finset you have not seen before. The same
technique works regardless of which specific numbers appear: rewrite
with `Finset.mem_insert` (or let `simp` handle the chain of
disjunctions) until you find the matching element.

**Retrieval check**: This level retrieved the membership rewriting
move (V5) on a fresh surface form.
"

DisabledTactic trivial decide native_decide aesop simp_all
