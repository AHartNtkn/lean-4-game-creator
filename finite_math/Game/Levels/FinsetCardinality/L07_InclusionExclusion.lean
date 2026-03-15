import GameServer.Commands
import Mathlib

World "FinsetCardinality"
Level 7

Title "Inclusion-exclusion"

Introduction
"
# The inclusion-exclusion principle

This is the central identity of cardinality theory for finite sets.

## The principle

When you take the union of two sets `s` and `t`, elements in the overlap
`s ∩ t` are counted once in `s` and once in `t`, but only once in `s ∪ t`.
This gives the fundamental identity:

```
|s ∪ t| + |s ∩ t| = |s| + |t|
```

In Lean, this is:

```
Finset.card_union_add_card_inter :
  (s ∪ t).card + (s ∩ t).card = s.card + t.card
```

## The additive form

Notice that Lean states this in **additive** form: both sides are sums.
In ordinary math, you often see the **subtractive** form:

```
|s ∪ t| = |s| + |t| - |s ∩ t|
```

The additive form avoids subtraction on natural numbers (which can
underflow), so it is cleaner in Lean.

## Your task

Prove the inclusion-exclusion identity for two specific finsets:
`s = {1, 2, 3}` and `t = {2, 3, 4}`.

Their union is `{1, 2, 3, 4}` (4 elements) and their intersection is
`{2, 3}` (2 elements). So `4 + 2 = 3 + 3`. Verify this using the
general lemma.
"

/-- Inclusion-exclusion for {1,2,3} and {2,3,4}. -/
Statement : (({1, 2, 3} : Finset Nat) ∪ {2, 3, 4}).card +
    (({1, 2, 3} : Finset Nat) ∩ {2, 3, 4}).card =
    ({1, 2, 3} : Finset Nat).card + ({2, 3, 4} : Finset Nat).card := by
  Hint "The goal is an instance of the inclusion-exclusion principle.
  What lemma directly states `(s ∪ t).card + (s ∩ t).card = s.card + t.card`?"
  Hint (hidden := true) "Use `rw [Finset.card_union_add_card_inter]`
  or `exact Finset.card_union_add_card_inter _ _`."
  exact Finset.card_union_add_card_inter _ _

Conclusion
"
You applied the inclusion-exclusion principle! The general lemma
`Finset.card_union_add_card_inter` immediately handles this, regardless
of which specific finsets are involved.

## Checking the numbers

For `s = {1, 2, 3}` and `t = {2, 3, 4}`:
- `s ∪ t = {1, 2, 3, 4}` has 4 elements
- `s ∩ t = {2, 3}` has 2 elements
- `s.card = 3`, `t.card = 3`
- `4 + 2 = 6 = 3 + 3` ✓

## Transfer moment

In ordinary math, inclusion-exclusion says:
```
|A ∪ B| = |A| + |B| - |A ∩ B|
```

The Lean version is the additive form:
```
|A ∪ B| + |A ∩ B| = |A| + |B|
```

Both express the same principle: elements in the overlap get counted
twice when you add `|A|` and `|B|`, so you must account for them. The
additive form avoids natural number subtraction, which makes it
more natural in Lean.

**In plain language**: \"When two sets overlap, the total count from the
union plus the overlap equals the sum of the individual counts. This is
because overlapping elements appear once in the union but contribute
to both individual counts.\"
"

/-- `Finset.card_union_add_card_inter` states that
`(s ∪ t).card + (s ∩ t).card = s.card + t.card`.

This is the **inclusion-exclusion principle** in additive form. It avoids
natural number subtraction.

The equivalent subtractive form is:
`(s ∪ t).card = s.card + t.card - (s ∩ t).card`. -/
TheoremDoc Finset.card_union_add_card_inter as "Finset.card_union_add_card_inter" in "Finset"

NewTheorem Finset.card_union_add_card_inter
DisabledTactic trivial decide native_decide aesop simp_all
