import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 4

Title "Reordering preserves multisets and finsets"

Introduction
"
# Permutation invariance

In Level 1, we saw that `[1, 2, 1, 3]` is a list with a specific order:
1 comes first, then 2, then 1 again, then 3.

But as a multiset, the order is irrelevant. The list `[3, 1, 2, 1]` --
which is the same elements in a different arrangement -- produces the
**same multiset**. And since both lists produce the same multiset, they
also produce the **same finset**.

## `Multiset.coe_eq_coe`

Recall from the Multisets and Hierarchy world:

```
Multiset.coe_eq_coe : (↑l₁ : Multiset α) = ↑l₂ ↔ l₁.Perm l₂
```

Two coerced lists give equal multisets if and only if one is a
rearrangement (permutation) of the other.

## Your task

Prove two facts:
1. `↑[1, 2, 1, 3]` and `↑[3, 1, 2, 1]` are the same multiset.
2. `[1, 2, 1, 3].toFinset` and `[3, 1, 2, 1].toFinset` are the same finset.

For the multiset equality, use `rw [Multiset.coe_eq_coe]` to reduce to a
permutation check, then `decide`. This is the **reduce-then-compute** pattern.

For the finset equality, `decide` can directly verify it, since both
sides evaluate to the same concrete finset `{1, 2, 3}`.
"

/-- The lists `[1, 2, 1, 3]` and `[3, 1, 2, 1]` produce the same multiset and the same finset. -/
Statement : (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) =
    ↑([3, 1, 2, 1] : List Nat) ∧
    ([1, 2, 1, 3] : List Nat).toFinset = ([3, 1, 2, 1] : List Nat).toFinset := by
  Hint "Use `constructor` to split the conjunction into two parts."
  constructor
  · Hint "The first goal is a multiset equality. What bridge lemma converts
    multiset equality to a list permutation check?"
    Hint (hidden := true) "Use `rw [Multiset.coe_eq_coe]` to reduce the
    multiset equality to a permutation check."
    rw [Multiset.coe_eq_coe]
    Hint "The goal is now `[1, 2, 1, 3].Perm [3, 1, 2, 1]`. This is a
    decidable proposition about concrete lists. Use `decide` to verify
    that one list is a rearrangement of the other."
    decide
  · Hint "The second goal asks whether the two lists produce the same finset.
    Both `[1, 2, 1, 3].toFinset` and `[3, 1, 2, 1].toFinset` evaluate to
    the same concrete finset (both contain exactly 1, 2, and 3). This is
    a decidable equality on concrete data."
    Hint (hidden := true) "Try `decide`. It evaluates both `toFinset`
    operations and confirms the resulting finsets are equal."
    decide

Conclusion
"
The multiset and finset do not care about order:

```
[1, 2, 1, 3]  ──↑──▶  {1, 2, 1, 3}  ──toFinset──▶  {1, 2, 3}
                           ‖                             ‖
[3, 1, 2, 1]  ──↑──▶  {3, 1, 2, 1}  ──toFinset──▶  {1, 2, 3}
```

The two lists are different as lists (different first elements, different
last elements), but they produce the **same multiset** and the **same finset**.

**What does NOT change under reordering**:
- Multiset: same (order is forgotten)
- Finset: same (already forgets order)
- Cardinality: same (4 and 3 respectively)
- Membership: same (`2 ∈` both)
- Count: same (`count 1 = 2` in both)

**What DOES change**:
- Only the list representation. `[1, 2, 1, 3] ≠ [3, 1, 2, 1]` as lists.

**Proof patterns used**:
1. `rw [Multiset.coe_eq_coe]; decide` -- **reduce-then-compute** for multiset equality
2. `decide` -- direct computation for finset equality

**In plain language**: \"Rearranging the elements of a bag does not change
the bag. And since the set of distinct elements does not depend on order,
it does not change either.\"
"

DisabledTactic trivial native_decide simp aesop simp_all
