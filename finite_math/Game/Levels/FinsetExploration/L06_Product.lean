import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 6

Title "Product of finsets"

Introduction
"
# The Cartesian product {1, 2} ×ˢ {3, 4}

Here is another preview: the **Cartesian product** of two finsets.

## `Finset.product`

Given finsets `s : Finset α` and `t : Finset β`, the product
`s ×ˢ t` (notation for `Finset.product s t`) is the finset of all
pairs `(a, b)` with `a ∈ s` and `b ∈ t`.

The key membership lemma is:

```
Finset.mem_product : (a, b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t
```

And the cardinality formula is:

```
Finset.card_product : (s ×ˢ t).card = s.card * t.card
```

## Your task

Prove two things:
1. The pair `(1, 4)` belongs to `{1, 2} ×ˢ {3, 4}`.
2. The cardinality of `{1, 2} ×ˢ {3, 4}` equals
   `{1, 2}.card * {3, 4}.card`.
"

/-- (1, 4) belongs to {1,2} ×ˢ {3,4} and the product has the right cardinality. -/
Statement : ((1, 4) : Nat × Nat) ∈ ({1, 2} : Finset Nat) ×ˢ ({3, 4} : Finset Nat) ∧
    (({1, 2} : Finset Nat) ×ˢ ({3, 4} : Finset Nat)).card =
      ({1, 2} : Finset Nat).card * ({3, 4} : Finset Nat).card := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "The first goal asks whether `(1, 4)` belongs to the product.
    Use `Finset.mem_product` to split this into two membership checks:
    `1` is in the first factor and `4` is in the second."
    Hint (hidden := true) "Use `rw [Finset.mem_product]` then `constructor`."
    rw [Finset.mem_product]
    Hint "Now prove the conjunction: `1` is in the first factor and `4`
    is in the second."
    Hint (hidden := true) "Use `constructor` then
    `simp [Finset.mem_insert, Finset.mem_singleton]` for each part."
    constructor
    · simp [Finset.mem_insert, Finset.mem_singleton]
    · simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "The second goal is a cardinality equation. The general lemma
    `Finset.card_product` says `(s ×ˢ t).card = s.card * t.card`.
    Apply it directly."
    Hint (hidden := true) "Use `rw [Finset.card_product]`."
    rw [Finset.card_product]

Conclusion
"
You proved two facts about the Cartesian product:

1. **Membership**: `(1, 4)` belongs to the product because `1` is in the
   first factor and `4` is in the second. The lemma `Finset.mem_product`
   decomposes product membership into component membership.

2. **Cardinality**: `|s ×ˢ t| = |s| * |t|`. Here, both factors have
   2 elements, so the product has 4 pairs:
   `(1,3), (1,4), (2,3), (2,4)`.

## Preview

The Cartesian product is fundamental for counting: the number of ways
to choose one element from each of two sets is the product of their
sizes. This is the **multiplication principle** of combinatorics.

You will see products again when counting functions between finite types
(a function `Fin m -> Fin n` is a choice of one output for each input)
and when working with matrices.

**In plain language**: \"The Cartesian product of two 2-element sets
has 2 * 2 = 4 elements. The pair (1, 4) is one of them, because 1 is
in the first set and 4 is in the second.\"
"

/-- `Finset.product s t` (notation: `s ×ˢ t`) is the finset of all pairs
`(a, b)` with `a ∈ s` and `b ∈ t`.

Use `Finset.mem_product` for membership:
`(a, b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t`.

Use `Finset.card_product` for counting:
`(s ×ˢ t).card = s.card * t.card`. -/
DefinitionDoc Finset.product as "Finset.product"

/-- `Finset.mem_product` states that
`(a, b) ∈ s ×ˢ t ↔ a ∈ s ∧ b ∈ t`.

A pair belongs to the product exactly when each component belongs to the
corresponding factor. -/
TheoremDoc Finset.mem_product as "Finset.mem_product" in "Finset"

/-- `Finset.card_product` states that
`(s ×ˢ t).card = s.card * t.card`.

The number of pairs in the Cartesian product equals the product of the
factor sizes. -/
TheoremDoc Finset.card_product as "Finset.card_product" in "Finset"

NewDefinition Finset.product
NewTheorem Finset.mem_product Finset.card_product
DisabledTactic trivial decide native_decide aesop simp_all
