import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 2

Title "Multiset membership"

Introduction
"
# Membership in a multiset

Membership is the most fundamental operation on any collection type.
You saw `List.Mem` (written `a ∈ l`) in the Lists world. Multisets
have an analogous notion: `a ∈ m` for `m : Multiset α`.

## The bridge lemma: `Multiset.mem_coe`

When you coerce a list to a multiset, membership is preserved:

```
Multiset.mem_coe : a ∈ (↑l : Multiset α) ↔ a ∈ l
```

This says: an element belongs to the multiset `↑l` if and only if it
belongs to the original list `l`. Coercion does not add or remove elements --
it only forgets the order.

## Your task

Prove that `2 ∈ (↑[1, 2, 3] : Multiset Nat)`.

**Strategy**: Use `rw [Multiset.mem_coe]` to reduce multiset membership
to list membership, then close with `decide`.
"

/-- The element `2` is in the multiset `↑[1, 2, 3]`. -/
Statement : (2 : Nat) ∈ (↑([1, 2, 3] : List Nat) : Multiset Nat) := by
  Hint "The goal asks about membership in a multiset that was coerced from
  a list. What lemma converts multiset membership back to list membership?"
  Hint (hidden := true) "Use `rw [Multiset.mem_coe]` to convert the multiset
  membership `2 ∈ ↑[1, 2, 3]` into the list membership `2 ∈ [1, 2, 3]`."
  rw [Multiset.mem_coe]
  Hint "Now the goal is `2 ∈ [1, 2, 3]`, which is a concrete list membership
  check. Try `decide`."
  decide

Conclusion
"
The proof followed a two-step pattern:

1. **Reduce**: `rw [Multiset.mem_coe]` converted `2 ∈ ↑[1, 2, 3]` (multiset
   membership) into `2 ∈ [1, 2, 3]` (list membership).
2. **Compute**: `decide` verified the list membership.

This is your first example of a pattern you will see repeatedly in this world:
**reduce** a multiset question to a list question using a bridge lemma, then
**compute** the list answer. We will name this pattern formally later.

The lemma `Multiset.mem_coe` is the membership analogue of `Multiset.coe_eq_coe`
(which you will see next). Together, they form the bridge between lists and multisets:
- `mem_coe`: element membership is preserved
- `coe_eq_coe`: equality is determined by permutation

**In plain language**: \"If an item is in the list, it is in the bag. If an item
is in the bag, it was in the list. Converting a list to a bag does not add
or remove items.\"
"

/-- `Multiset.mem_coe` states that `a ∈ (↑l : Multiset α) ↔ a ∈ l`.
Membership in a coerced multiset is the same as membership in the original list.
Use `rw [Multiset.mem_coe]` to convert multiset membership to list membership. -/
TheoremDoc Multiset.mem_coe as "Multiset.mem_coe" in "Multiset"

NewTheorem Multiset.mem_coe
DisabledTactic trivial native_decide simp aesop simp_all
