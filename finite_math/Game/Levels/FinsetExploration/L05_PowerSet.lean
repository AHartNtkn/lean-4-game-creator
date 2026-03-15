import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 5

Title "Power set preview"

Introduction
"
# How many subsets does {1, 2, 3} have?

Here is a preview of an operation you will study in depth later:
the **power set**.

## `Finset.powerset`

Given a finset `s`, `s.powerset` is the finset of all sub-finsets of `s`.
For example, `{1, 2}.powerset` contains:
- `∅`, `{1}`, `{2}`, `{1, 2}`

That is 4 = 2² subsets.

## The formula

A finite set with `n` elements has exactly `2^n` subsets. In Lean:

```
Finset.card_powerset : s.powerset.card = 2 ^ s.card
```

## Your task

Prove that `{1, 2, 3}.powerset` has exactly 8 elements (since 2³ = 8).

**Strategy**: Rewrite with `Finset.card_powerset` to reduce the goal to
`2 ^ {1, 2, 3}.card = 8`, then compute the cardinality and simplify.
"

/-- The powerset of {1, 2, 3} has 8 elements. -/
Statement : ({1, 2, 3} : Finset Nat).powerset.card = 8 := by
  Hint "The key lemma is `Finset.card_powerset`, which says
  `s.powerset.card = 2 ^ s.card`. Rewrite with it."
  Hint (hidden := true) "Use `rw [Finset.card_powerset]`."
  rw [Finset.card_powerset]
  Hint "The goal is now `2 ^ s.card = 8` where `s` is our three-element
  finset. The cardinality of the literal finset reduces by computation,
  and `2 ^ 3 = 8` is definitional."
  Hint (hidden := true) "The goal reduces definitionally. Try `rfl`."
  rfl

Conclusion
"
You proved that {1, 2, 3} has 8 subsets. The proof used the general
formula `Finset.card_powerset`:

```
s.powerset.card = 2 ^ s.card
```

Since `{1, 2, 3}.card = 3` and `2³ = 8`, the result follows.

## The 8 subsets

For reference, the 8 subsets of {1, 2, 3} are:
| Size 0 | Size 1 | Size 2 | Size 3 |
|--------|--------|--------|--------|
| ∅ | {1} | {1,2} | {1,2,3} |
|   | {2} | {1,3} | |
|   | {3} | {2,3} | |

## Preview

The powerset operation will be studied more carefully in a later world,
where you will work with `Finset.mem_powerset` and prove results about
subsets of specific finsets. For now, the key takeaway is:

**A set with n elements has 2^n subsets.**

**In plain language**: \"The set {1, 2, 3} has 8 subsets: the empty set,
three singletons, three pairs, and the full set. This is 2³ = 8, an
instance of the general formula.\"
"

/-- `Finset.powerset` maps a finset `s` to the finset of all its sub-finsets.

`s.powerset` contains every finset `t` such that `t ⊆ s`.

Use `Finset.mem_powerset` to reason about membership:
`t ∈ s.powerset ↔ t ⊆ s`.

Use `Finset.card_powerset` for counting:
`s.powerset.card = 2 ^ s.card`. -/
DefinitionDoc Finset.powerset as "Finset.powerset"

/-- `Finset.card_powerset` states that `s.powerset.card = 2 ^ s.card`.

A finset with `n` elements has exactly `2^n` sub-finsets. -/
TheoremDoc Finset.card_powerset as "Finset.card_powerset" in "Finset"

NewDefinition Finset.powerset
NewTheorem Finset.card_powerset
DisabledTactic trivial decide native_decide aesop simp_all
