import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 1

Title "Union membership"

Introduction
"
# Finset union: combining two finsets

You have learned to construct finsets, check membership, and use `simp`
to automate membership proofs. Now we begin studying **operations** on
finsets: ways to build new finsets from old ones.

## The union operation

Given finsets `s` and `t`, their **union** `s ∪ t` contains every element
that belongs to at least one of them. The key membership lemma is:

```
Finset.mem_union : a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t
```

This is the finset analogue of the set-theory fact: an element belongs
to a union if and only if it belongs to at least one of the two sets.

## Notation

The symbol `∪` is typed `\\cup` or `\\union`. You will also see
`∩` (intersection) and `\\` (set difference) in later levels.

## Your task

Given two concrete finsets `s = {1, 2, 3}` and `t = {3, 4, 5}`, prove
that `2 ∈ s ∪ t`.

**Strategy**: Rewrite with `Finset.mem_union` to turn the goal into
a disjunction, then choose the left branch (since `2 ∈ s`), and close
with `simp`.
"

/-- `2` belongs to the union of `{1, 2, 3}` and `{3, 4, 5}`. -/
Statement : 2 ∈ ({1, 2, 3} : Finset Nat) ∪ {3, 4, 5} := by
  Hint "The goal asks whether `2` belongs to the union of the finsets
  containing 1, 2, 3 and 3, 4, 5. Use `Finset.mem_union` to rewrite
  the union membership into a disjunction: `2` is in the first finset
  or `2` is in the second finset."
  Hint (hidden := true) "Use `rw [Finset.mem_union]`."
  rw [Finset.mem_union]
  Hint "The goal is now a disjunction. Since `2` is in the first finset,
  choose the left branch."
  Hint (hidden := true) "Use `left`."
  left
  Hint "Now prove that `2` belongs to the finset containing 1, 2, 3.
  You know how to do this from the Membership world."
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You proved your first union membership fact. The proof followed three steps:

1. **Rewrite** with `Finset.mem_union` to expose the disjunction.
2. **Choose a branch** with `left` (since `2` is in the first finset).
3. **Close** the membership with `simp`.

The key insight: membership in `s ∪ t` reduces to membership in `s` **or**
membership in `t`. This is the finset version of the familiar set-theory
fact.

**In plain language**: \"2 is in {1, 2, 3} ∪ {3, 4, 5} because 2 is in
{1, 2, 3}.\"
"

/-- `Finset.mem_union` states that `a ∈ s ∪ t ↔ a ∈ s ∨ a ∈ t`.

An element belongs to the union of two finsets exactly when it belongs
to at least one of them. Use `rw [Finset.mem_union]` to convert a
union membership goal into a disjunction. -/
TheoremDoc Finset.mem_union as "Finset.mem_union" in "Finset"

NewTheorem Finset.mem_union
DisabledTactic trivial decide native_decide aesop simp_all
