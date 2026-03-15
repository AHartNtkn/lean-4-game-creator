import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 4

Title "Combining operations"

Introduction
"
# Multi-step membership reasoning

Now that you know the membership lemmas for `∪`, `∩`, and `\\`, you can
handle goals that combine multiple operations. The idea is simple:
apply the membership lemmas from the outside in, reducing each
operation to its logical connective.

## Your task

Given `s = {1, 2, 3}`, `t = {3, 4, 5}`, and `u = {2, 3}`, prove that
`3 ∈ (s ∪ t) ∩ u`.

**Strategy**: First rewrite with `Finset.mem_inter` (since `∩` is the
outermost operation), then split, and handle the union in the first
subgoal with `Finset.mem_union`.
"

/-- `3` belongs to `({1, 2, 3} ∪ {3, 4, 5}) ∩ {2, 3}`. -/
Statement : 3 ∈ (({1, 2, 3} : Finset Nat) ∪ {3, 4, 5}) ∩ {2, 3} := by
  Hint "The outermost operation is `∩`. Rewrite with `Finset.mem_inter`
  to split into two parts: `3` is in the union and `3` is in the
  finset containing 2, 3."
  Hint (hidden := true) "Use `rw [Finset.mem_inter]`."
  rw [Finset.mem_inter]
  Hint "Now split the conjunction."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "The first subgoal involves the union. Rewrite with
    `Finset.mem_union` to get a disjunction, then choose a branch."
    Hint (hidden := true) "Use `rw [Finset.mem_union]`, then `left`."
    rw [Finset.mem_union]
    left
    Hint "Now prove that `3` belongs to the finset containing 1, 2, 3."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Prove that `3` belongs to the finset containing 2, 3."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You combined intersection and union in a single proof. The recipe is
always the same:

1. Identify the **outermost** operation and apply its membership lemma.
2. Handle each resulting subgoal, which may involve further operations.
3. At the base, close concrete membership goals with `simp`.

The outermost operation determines the **shape** of the proof:
- If the outer operation is `∩`, you must prove **both** parts (conjunction).
- If the outer operation is `∪`, you choose **one** part (disjunction).
- If the outer operation is `\\`, you prove membership **and** non-membership.

**In plain language**: \"3 is in ({1,2,3} ∪ {3,4,5}) ∩ {2,3} because
3 is in the union (it's in {1,2,3}) and 3 is in {2,3}.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
