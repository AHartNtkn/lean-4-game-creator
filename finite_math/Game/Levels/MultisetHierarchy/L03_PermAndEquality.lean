import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 3

Title "Permutations and multiset equality"

Introduction
"
# When are two multisets equal?

Two multisets are equal when they contain the same elements with the same
multiplicities -- regardless of order. In Lean, this is captured by the
fact that `Multiset α` is a quotient by `List.Perm`:

If `l₁.Perm l₂` (the lists are permutations of each other), then
`(↑l₁ : Multiset α) = ↑l₂`.

## `List.Perm`

`List.Perm l₁ l₂` asserts that `l₁` can be rearranged into `l₂`.
For concrete lists with decidable equality, `decide` can verify this.

## `Multiset.coe_eq_coe`

The key lemma is `Multiset.coe_eq_coe`:

```
(↑l₁ : Multiset α) = ↑l₂ ↔ l₁.Perm l₂
```

This lets you convert between multiset equality and list permutation.

## Your task

Prove that the lists `[1, 2, 3]` and `[3, 1, 2]` give the same multiset.

**Strategy**: Use `rw [Multiset.coe_eq_coe]` to reduce multiset equality
to a list permutation, then `decide` to verify the permutation.
"

/-- The lists `[1, 2, 3]` and `[3, 1, 2]` produce the same multiset. -/
Statement : (↑([1, 2, 3] : List Nat) : Multiset Nat) = ↑([3, 1, 2] : List Nat) := by
  Hint "The goal is an equality between two multisets, each coerced from a list.
  What lemma converts multiset equality to a statement about list permutations?"
  Hint (hidden := true) "Use `rw [Multiset.coe_eq_coe]` to convert the multiset
  equality into a list permutation."
  rw [Multiset.coe_eq_coe]
  Hint "Now the goal is `[1, 2, 3].Perm [3, 1, 2]`. This is a decidable proposition
  about concrete lists. Try `decide`."
  decide

Conclusion
"
The proof has two steps:

1. **Reduce**: `rw [Multiset.coe_eq_coe]` converted the multiset equality
   `↑[1, 2, 3] = ↑[3, 1, 2]` into the proposition `[1, 2, 3].Perm [3, 1, 2]`.

2. **Compute**: `decide` verified that the second list is indeed a
   rearrangement of the first.

Notice this is the same **reduce-then-compute** pattern from Level 2:
use a bridge lemma to convert a multiset question into a list question,
then compute the answer.

**Proof move**: The pattern `rw [bridge_lemma]; decide` recurs throughout
this world. The bridge lemma converts between the quotient world (multisets)
and the concrete world (lists), and `decide` handles the concrete check.
Remember this shape.

**In plain language**: \"The bag containing 1, 2, and 3 is the same
regardless of the order you put the items in.\"
"

/-- `Multiset.coe_eq_coe` states that `(↑l₁ : Multiset α) = ↑l₂ ↔ l₁.Perm l₂`.
Two coerced lists give equal multisets if and only if the lists are permutations
of each other. Use `rw [Multiset.coe_eq_coe]` to reduce multiset equality to
a permutation check. -/
TheoremDoc Multiset.coe_eq_coe as "Multiset.coe_eq_coe" in "Multiset"

/-- `List.Perm l₁ l₂` asserts that `l₁` is a rearrangement (permutation) of `l₂`.
Two lists are permutations of each other when they contain the same elements with
the same multiplicities, possibly in a different order.

For concrete lists with decidable element equality, `decide` can verify `List.Perm`. -/
DefinitionDoc List.Perm as "List.Perm"

NewTheorem Multiset.coe_eq_coe
NewDefinition List.Perm
DisabledTactic trivial native_decide simp aesop simp_all
