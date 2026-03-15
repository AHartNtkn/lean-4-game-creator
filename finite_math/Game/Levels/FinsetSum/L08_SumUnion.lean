import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 8

Title "sum_union for disjoint sets"

Introduction
"
# Splitting a sum over a disjoint union

When two finsets `s` and `t` are **disjoint** (meaning `s ∩ t = ∅`),
the sum over their union splits cleanly:

```
Finset.sum_union (h : Disjoint s t) :
  ∑ x ∈ s ∪ t, f x = (∑ x ∈ s, f x) + ∑ x ∈ t, f x
```

This is the big-operator analogue of cardinality addition for disjoint
sets: `(s ∪ t).card = s.card + t.card`.

## Disjointness

Two finsets are disjoint when `Disjoint s t`, which means `s ∩ t ≤ ⊥`
(i.e., `s ∩ t = ∅`). For concrete finsets like `{1, 2}` and `{3, 4}`,
this can be verified using `Finset.disjoint_left` and membership reasoning.

## Your task

Prove the sum-splitting identity for two concrete disjoint finsets.
"

/-- Splitting a sum over a disjoint union. -/
Statement : ∑ x ∈ ({1, 2} : Finset Nat) ∪ {3, 4}, x =
    (∑ x ∈ ({1, 2} : Finset Nat), x) + ∑ x ∈ ({3, 4} : Finset Nat), x := by
  Hint "Apply `Finset.sum_union` with a proof of disjointness.
  You can establish disjointness with `norm_num [Finset.disjoint_left]`.

  Try:
  `have hd : Disjoint ... ... := by norm_num [Finset.disjoint_left]`
  then use `exact Finset.sum_union hd`."
  Hint (hidden := true) "Try:
  `have hd : Disjoint (insert 1 (singleton 2) : Finset Nat) (insert 3 (singleton 4) : Finset Nat) := by norm_num [Finset.disjoint_left]`
  then `exact Finset.sum_union hd`."
  have hd : Disjoint ({1, 2} : Finset Nat) ({3, 4} : Finset Nat) := by
    norm_num [Finset.disjoint_left]
  exact Finset.sum_union hd

Conclusion
"
You split a sum over a disjoint union into two separate sums.

## The disjointness requirement

`sum_union` only works when `s` and `t` are disjoint. If they overlap,
an element in `s ∩ t` would be counted once in `∑ x ∈ s ∪ t, f x`
but appears in both `∑ x ∈ s, f x` and `∑ x ∈ t, f x`, so the
equation would fail.

## Comparison with cardinality

Cardinality is the special case of summing the constant function `1`:
- `card_union_of_disjoint` says `(s ∪ t).card = s.card + t.card`
- `sum_union` says `∑ x ∈ s ∪ t, f x = (∑ x ∈ s, f x) + ∑ x ∈ t, f x`

**In plain language**: \"When two sets don't overlap, the total sum
splits into the sum over each part. This is the additive analogue of
the cardinality formula for disjoint unions.\"
"

/-- `Finset.sum_union` states that if `Disjoint s t`, then
`∑ x ∈ s ∪ t, f x = (∑ x ∈ s, f x) + ∑ x ∈ t, f x`.

This splits a sum over a disjoint union into two sums. -/
TheoremDoc Finset.sum_union as "Finset.sum_union" in "Finset"

NewTheorem Finset.sum_union
DisabledTactic trivial decide native_decide simp aesop simp_all
