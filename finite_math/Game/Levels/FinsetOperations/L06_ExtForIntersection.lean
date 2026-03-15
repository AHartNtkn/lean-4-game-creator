import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 6

Title "ext for intersection"

Introduction
"
# Commutativity of intersection

Let's practice the `ext` proof pattern on a different operation.

## Your task

Prove that `s ∩ t = t ∩ s` for arbitrary finsets `s` and `t`. This is
the **commutativity of intersection**.

The proof shape is the same as for union commutativity, but now the
membership lemma gives a **conjunction** instead of a disjunction.
After `rcases h with ⟨hs, ht⟩` (splitting a conjunction), you rebuild
the conjunction with the pieces swapped using `exact ⟨ht, hs⟩`.

## The angle bracket syntax

To split a conjunction hypothesis `h : P ∧ Q`, use:
```
rcases h with ⟨hp, hq⟩
```
This gives you `hp : P` and `hq : Q`.

To prove a conjunction goal `P ∧ Q` when you already have the parts,
use:
```
exact ⟨proof_of_P, proof_of_Q⟩
```

The angle brackets `⟨ ⟩` are typed `\\<` and `\\>` (or `\\langle` and
`\\rangle`).
"

/-- Intersection of finsets is commutative. -/
Statement (s t : Finset Nat) : s ∩ t = t ∩ s := by
  Hint "Use `ext a` to reduce the equality to a membership biconditional."
  Hint (hidden := true) "Use `ext a`."
  ext a
  Hint "Now split the biconditional with `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "Prove `a ∈ s ∩ t → a ∈ t ∩ s`. Start by introducing the
    hypothesis."
    Hint (hidden := true) "Use `intro h`."
    intro h
    Hint "Rewrite `h` with `mem_inter` to get a conjunction, then
    split it into its two parts."
    Hint (hidden := true) "Use `rw [Finset.mem_inter] at h`,
    then `rcases h with ⟨hs, ht⟩`."
    rw [Finset.mem_inter] at h
    rcases h with ⟨hs, ht⟩
    Hint "Now you have `hs : a ∈ s` and `ht : a ∈ t`. The goal asks
    for `a ∈ t ∩ s`. Rewrite the goal and provide the pair in
    swapped order."
    Hint (hidden := true) "Use `rw [Finset.mem_inter]`, then
    `exact ⟨ht, hs⟩`."
    rw [Finset.mem_inter]
    exact ⟨ht, hs⟩
  · Hint "The reverse direction is symmetric. Follow the same pattern."
    Hint (hidden := true) "Use `intro h`, `rw [Finset.mem_inter] at h`,
    `rcases h with ⟨ht, hs⟩`, `rw [Finset.mem_inter]`,
    `exact ⟨hs, ht⟩`."
    intro h
    rw [Finset.mem_inter] at h
    rcases h with ⟨ht, hs⟩
    rw [Finset.mem_inter]
    exact ⟨hs, ht⟩

Conclusion
"
The proof of intersection commutativity follows the same `ext` pattern
as union commutativity, but the membership logic is different:

- **Union**: membership is a disjunction → use `rcases` with `|` and
  swap the branches.
- **Intersection**: membership is a conjunction → use `rcases` with
  `⟨ , ⟩` to split, then rebuild with swapped components.

## The proof recipe for `ext`

1. `ext a` -- reduce to membership.
2. `constructor` -- split the biconditional.
3. In each direction:
   a. `intro h` -- introduce the hypothesis.
   b. `rw [mem_*] at h` -- expand membership in the hypothesis.
   c. `rcases h with ...` -- destructure the logical form.
   d. `rw [mem_*]` -- expand membership in the goal.
   e. Rebuild with the pieces rearranged.

This recipe handles **any** finset equality that follows from
membership lemmas.

**In plain language**: \"s ∩ t = t ∩ s because being in both s and t is
the same as being in both t and s.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
