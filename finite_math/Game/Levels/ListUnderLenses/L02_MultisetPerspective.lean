import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 2

Title "As a Multiset"

Introduction
"
# The multiset lens

Now let us look at `[1, 2, 1, 3]` through the **multiset** lens.

Recall from the Multisets and Hierarchy world:
- A multiset forgets **order** but keeps **multiplicity**.
- Convert a list to a multiset using the coercion `↑`.
- `Multiset.card` counts elements (with multiplicity).
- `Multiset.mem_coe` converts multiset membership back to list membership.

## What changes?

When we coerce `[1, 2, 1, 3]` to a multiset:
- The **order** is forgotten. We can no longer say \"the first element is 1.\"
- The **multiplicity** is preserved: `1` still appears twice, and `2` and `3`
  each appear once.
- The **cardinality** is still 4 (same as the list length).

## What stays the same?

- Membership: `2 ∈ ↑[1, 2, 1, 3]` still holds.
- Cardinality: `Multiset.card ↑[1, 2, 1, 3] = 4`.

## Your task

Prove two facts about `[1, 2, 1, 3]` viewed as a multiset:
1. Its multiset cardinality equals the original list length.
2. The element `2` is a member of the multiset.

For cardinality, you will find that `Multiset.card (↑l) = l.length` is
true **by definition** -- the coercion preserves the count. For membership,
you will need the **reduce-then-compute** pattern from the Multisets world.
"

/-- The multiset `↑[1, 2, 1, 3]` has the same cardinality as the list's length, and contains 2. -/
Statement : Multiset.card (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) =
    ([1, 2, 1, 3] : List Nat).length ∧
    (2 : Nat) ∈ (↑([1, 2, 1, 3] : List Nat) : Multiset Nat) := by
  Hint "Use `constructor` to split the conjunction into two subgoals."
  constructor
  · Hint "The first goal asks whether the multiset cardinality equals the
    list length. The key fact is that `Multiset.card (↑l)` is **definitionally
    equal** to `l.length` -- the coercion to a multiset does not change the
    count of elements. Since both sides compute to the same value by definition,
    which tactic closes this?"
    Hint (hidden := true) "Try `rfl`. The multiset cardinality of a coerced list
    equals the list length by definition -- no lemma is needed."
    rfl
  · Hint "The goal is `2 ∈ ↑[1, 2, 1, 3]` -- membership in a multiset.
    You cannot directly evaluate multiset membership. Instead, use the
    bridge lemma `Multiset.mem_coe` to **reduce** it to list membership,
    then **compute** the list check."
    Hint (hidden := true) "Use `rw [Multiset.mem_coe]` to convert the multiset
    membership `2 ∈ ↑[1, 2, 1, 3]` into the list membership `2 ∈ [1, 2, 1, 3]`."
    rw [Multiset.mem_coe]
    Hint "The goal is now `2 ∈ [1, 2, 1, 3]` -- a list membership check.
    Use `decide` to verify it."
    decide

Conclusion
"
Compare the **list** and **multiset** views:

```
List    [1, 2, 1, 3]     length = 4     2 ∈ l ✓
           ↓ ↑
Multiset {1, 2, 1, 3}    card = 4       2 ∈ ↑l ✓
```

Both have cardinality 4, and both contain 2. The coercion `↑` preserved
the elements and their multiplicities -- only the order was discarded.

## Why did `rfl` work for cardinality?

The cardinality part was proved by `rfl`, meaning both sides are
**definitionally equal**. This is because `Multiset.card` is defined as
the length of any representing list, and `↑l` is represented by `l` itself.
So `Multiset.card (↑l)` unfolds to `l.length` without needing any lemma.

This is different from the membership proof, where `rfl` would not work
because multiset membership is defined via the quotient structure, not by
simple unfolding. That is why we needed `Multiset.mem_coe` as a bridge.

## Proof pattern: reduce-then-compute

For membership, you used the **reduce-then-compute** pattern from the
Multisets world:
1. `rw [Multiset.mem_coe]` -- **reduce** multiset membership to list membership
2. `decide` -- **compute** the list membership check

**In plain language**: \"Putting the items 1, 2, 1, 3 into a bag gives a
bag with 4 items (including the extra 1). The number 2 is still in the bag.\"

In the next level, you will apply the **finset** lens and see what happens
when duplicates are removed.
"

DisabledTactic trivial native_decide simp aesop simp_all
