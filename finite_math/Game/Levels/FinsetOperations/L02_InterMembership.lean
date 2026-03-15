import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 2

Title "Intersection membership"

Introduction
"
# Finset intersection: elements in both

The **intersection** `s ∩ t` contains exactly the elements that belong
to **both** `s` and `t`. The membership lemma is:

```
Finset.mem_inter : a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t
```

Notice the logical connective changed: union uses `∨` (or), intersection
uses `∧` (and). This mirrors the set-theory definitions exactly.

## Notation

The symbol `∩` is typed `\\cap` or `\\inter`.

## Your task

Given `s = {1, 2, 3}` and `t = {2, 3, 4}`, prove that `3 ∈ s ∩ t`.

**Strategy**: Rewrite with `Finset.mem_inter` to turn the goal into
a conjunction, then split with `constructor` and prove each part.
"

/-- `3` belongs to the intersection of `{1, 2, 3}` and `{2, 3, 4}`. -/
Statement : 3 ∈ ({1, 2, 3} : Finset Nat) ∩ {2, 3, 4} := by
  Hint "The goal asks whether `3` belongs to the intersection of
  the finsets containing 1, 2, 3 and 2, 3, 4. Rewrite with
  `Finset.mem_inter` to turn this into a conjunction: `3` is in the
  first finset **and** `3` is in the second finset."
  Hint (hidden := true) "Use `rw [Finset.mem_inter]`."
  rw [Finset.mem_inter]
  Hint "The goal is now a conjunction of two membership claims. Split
  the conjunction into two subgoals using `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "Prove that `3` belongs to the finset containing 1, 2, 3."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Prove that `3` belongs to the finset containing 2, 3, 4."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You proved your first intersection membership fact. The proof pattern is:

1. **Rewrite** with `Finset.mem_inter` to expose the conjunction.
2. **Split** with `constructor` into two membership subgoals.
3. **Close** each membership with `simp`.

Compare with union: union gives a disjunction (`∨`), so you choose one
branch. Intersection gives a conjunction (`∧`), so you must prove **both**
parts.

**In plain language**: \"3 is in {1, 2, 3} ∩ {2, 3, 4} because 3 is in
{1, 2, 3} **and** 3 is in {2, 3, 4}.\"
"

/-- `Finset.mem_inter` states that `a ∈ s ∩ t ↔ a ∈ s ∧ a ∈ t`.

An element belongs to the intersection of two finsets exactly when it
belongs to both of them. Use `rw [Finset.mem_inter]` to convert an
intersection membership goal into a conjunction. -/
TheoremDoc Finset.mem_inter as "Finset.mem_inter" in "Finset"

NewTheorem Finset.mem_inter
DisabledTactic trivial decide native_decide aesop simp_all
