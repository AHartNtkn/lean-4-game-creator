import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 2

Title "prod_empty and prod_singleton"

Introduction
"
# Empty products and singleton products

## Empty product

The product over an empty set is `1` (the neutral element for
multiplication), just as the sum over an empty set is `0`:

```
Finset.prod_empty : ∏ x ∈ ∅, f x = 1
```

## Your task

Prove that `∏ x ∈ (∅ : Finset Nat), (x + 1) = 1`.

Use `rw [Finset.prod_empty]` to rewrite the product.
"

/-- The product over an empty finset is `1`. -/
Statement : ∏ x ∈ (∅ : Finset Nat), (x + 1) = 1 := by
  Hint "The product over an empty set is `1`. Use `rw [Finset.prod_empty]`."
  Hint (hidden := true) "Try `rw [Finset.prod_empty]`."
  rw [Finset.prod_empty]

Conclusion
"
You verified that the empty product is `1`. The lemma is
`Finset.prod_empty`:

```
∏ x ∈ ∅, f x = 1
```

## Comparing the identities

| Operation | Empty result | Lemma |
|-----------|-------------|-------|
| Sum | `∑ x ∈ ∅, f x = 0` | `Finset.sum_empty` |
| Product | `∏ x ∈ ∅, f x = 1` | `Finset.prod_empty` |

The empty sum is `0` (additive identity) and the empty product is `1`
(multiplicative identity). These are the neutral elements of their
respective monoids.

## What comes next

Now that you can handle base cases, the next level introduces
`prod_range_succ` — the multiplicative analogue of `sum_range_succ`.
"

/-- `Finset.prod_empty` states that `∏ x ∈ ∅, f x = 1`.

The product over an empty finset is the multiplicative identity `1`. -/
TheoremDoc Finset.prod_empty as "Finset.prod_empty" in "Finset"

NewTheorem Finset.prod_empty
DisabledTactic trivial decide native_decide simp aesop simp_all
