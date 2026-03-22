import Game.Metadata

World "BigOpAlgebra"
Level 6

Title "Splitting by Disjoint Union"

Introduction "
# Summing Over a Union

If two finsets are **disjoint** (share no elements), the sum over
their union is the sum of the individual sums:

$$s \\cap t = \\emptyset \\implies \\sum_{x \\in s \\cup t} f(x) = \\sum_{x \\in s} f(x) + \\sum_{x \\in t} f(x)$$

In Lean:
```
Finset.sum_union (h : Disjoint s t) :
  ∑ x ∈ s ∪ t, f x = (∑ x ∈ s, f x) + ∑ x ∈ t, f x
```

The disjointness hypothesis `h` is essential — without it, elements
in the intersection would be counted twice on the left but only once
on the right.

**Your task**: Given that `s` and `t` are disjoint and you know
their individual sums, compute the union sum.
"

/-- Split a sum over a disjoint union into two parts. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ) (h : Disjoint s t)
    (hs : ∑ x ∈ s, f x = 10) (ht : ∑ x ∈ t, f x = 15) :
    ∑ x ∈ s ∪ t, f x = 25 := by
  Hint "Use `rw [Finset.sum_union h]` to split the union sum.
  The hypothesis `h : Disjoint s t` is needed as an argument."
  rw [Finset.sum_union h]
  Hint "Now substitute the known sums."
  Hint (hidden := true) "Try `rw [hs, ht]`."
  rw [hs, ht]

Conclusion "
`sum_union` is the partition principle for sums: if you can split
a finset into disjoint pieces, you can sum over each piece
separately.

This is the big-operator analogue of `card_union_of_disjoint`:
$$|s \\cup t| = |s| + |t|$$
which is the special case where `f = fun _ => 1`.

**The `Disjoint` hypothesis**: In Lean, `Disjoint s t` for finsets
means `s ∩ t = ∅`. This is a lattice-theoretic notion — finsets
form a lattice under `⊆`, where `∩` is the infimum. The
disjointness condition prevents double-counting.

**What if they're not disjoint?** The general formula is the
inclusion-exclusion identity for sums:
$$\\sum_{s \\cup t} f + \\sum_{s \\cap t} f = \\sum_s f + \\sum_t f$$
This is exactly the big-operator analogue of
`card_union_add_card_inter` from the Cardinality world.
`sum_union` is the special case where `s \\cap t = \\emptyset`,
so `\\sum_{s \\cap t} f = 0`.

**Multiplicative twin**: The product version is `Finset.prod_union`:
`∏ x ∈ s ∪ t, f x = (∏ x ∈ s, f x) * ∏ x ∈ t, f x`.
Same requirement: `Disjoint s t`.

| Additive | Multiplicative |
|----------|---------------|
| `sum_union h` | `prod_union h` |
| `∑(s ∪ t) = ∑s + ∑t` | `∏(s ∪ t) = ∏s · ∏t` |
"

/-- `Finset.sum_union` states that if `h : Disjoint s t`, then
`∑ x ∈ s ∪ t, f x = (∑ x ∈ s, f x) + ∑ x ∈ t, f x`.

## Syntax
```
rw [Finset.sum_union h]     -- where h : Disjoint s t
exact Finset.sum_union h
```

## When to use it
When the goal involves a sum over `s ∪ t` and you have (or can
prove) that `s` and `t` are disjoint. Splits the union sum into
two independent sums.

## Warning
The hypothesis `Disjoint s t` is required. Without it, elements
in the intersection would be counted differently on each side.
-/
TheoremDoc Finset.sum_union as "Finset.sum_union" in "BigOp"

/-- `Finset.prod_union` states that if `h : Disjoint s t`, then
`∏ x ∈ s ∪ t, f x = (∏ x ∈ s, f x) * ∏ x ∈ t, f x`.

The multiplicative twin of `Finset.sum_union`.

## Syntax
```
rw [Finset.prod_union h]     -- where h : Disjoint s t
exact Finset.prod_union h
```

## When to use it
When the goal involves a product over `s ∪ t` and `s` and `t` are
disjoint. Splits the union product into two independent products.
-/
TheoremDoc Finset.prod_union as "Finset.prod_union" in "BigOp"

NewTheorem Finset.sum_union Finset.prod_union

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
