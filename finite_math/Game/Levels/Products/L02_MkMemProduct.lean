import Game.Metadata

World "Products"
Level 2

Title "Building Product Pairs"

Introduction "
# The Forward Direction

In the previous level you used `Finset.mem_product` as a rewrite
to split product membership into a conjunction. There's a more
direct way when you already have both component memberships:

```
Finset.mk_mem_product : a ∈ s → b ∈ t → (a, b) ∈ s ×ˢ t
```

This takes two membership proofs and combines them in one step —
no need for `rw` + `constructor`.

**Your task**: Given `ha : 3 ∈ s` and `hb : 7 ∈ t`, prove
`(3, 7) ∈ s ×ˢ t`.
"

/-- Combine two membership proofs into product membership. -/
Statement (s t : Finset ℕ) (ha : 3 ∈ s) (hb : 7 ∈ t) :
    (3, 7) ∈ s ×ˢ t := by
  Hint "You have `ha : 3 ∈ s` and `hb : 7 ∈ t`. Use
  `Finset.mk_mem_product` to combine them directly."
  Hint (hidden := true) "Try `exact Finset.mk_mem_product ha hb`."
  exact Finset.mk_mem_product ha hb

Conclusion "
One line! `Finset.mk_mem_product ha hb` builds a product membership
from its components.

**When to use which**:
- `Finset.mem_product` (↔): when you need to rewrite or extract
  component memberships from a product membership
- `Finset.mk_mem_product` (→): when you already have both component
  memberships and want to build a product membership directly

Both encode the same mathematical fact — the definition of
Cartesian product — but they face different directions.
"

/-- `Finset.mk_mem_product` builds product membership from
component memberships:

`ha : a ∈ s → hb : b ∈ t → (a, b) ∈ s ×ˢ t`

## Syntax
```
exact Finset.mk_mem_product ha hb
```

## When to use it
When you have separate proofs of `a ∈ s` and `b ∈ t` and
need to show `(a, b) ∈ s ×ˢ t`.
-/
TheoremDoc Finset.mk_mem_product as "Finset.mk_mem_product" in "Product"

TheoremTab "Product"
NewTheorem Finset.mk_mem_product

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
