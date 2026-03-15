import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 1

Title "What is Finset.prod?"

Introduction
"
# Big products over finite sets

Welcome to the **Finset.prod** world! You already know how to sum over
finite sets using `∑ x ∈ s, f x`. This world introduces the
multiplicative counterpart:

$$\\prod_{x \\in s} f(x)$$

## The idea

In ordinary mathematics you write
$$\\prod_{x \\in \\{2, 3, 5\\}} x = 2 \\cdot 3 \\cdot 5 = 30.$$

In Lean 4 / mathlib this is captured by `Finset.prod`:

```
Finset.prod s f
```

which means \"multiply `f x` as `x` ranges over the elements of the
finset `s`.\" There is also notation:

```
∏ x ∈ s, f x
```

## The type-class requirement

While `Finset.sum` requires an `AddCommMonoid` (with `0` and `+`),
`Finset.prod` requires a `CommMonoid` (with `1` and `*`). The neutral
element for products is `1`, not `0`.

## Your first task

Prove that `∏ x ∈ ({3} : Finset Nat), x = 3`.

This is the product analogue of `sum_singleton`: the product over a
singleton is just the function value. The lemma is `Finset.prod_singleton`:

```
Finset.prod_singleton (f : ι → M) (a : ι) :
  ∏ x ∈ {a}, f x = f a
```
"

/-- The product over a singleton is that element. -/
Statement : ∏ x ∈ ({3} : Finset Nat), x = 3 := by
  Hint "The product over a singleton set equals the value at that element.
  Use `rw [Finset.prod_singleton]` to rewrite the product."
  Hint (hidden := true) "Try `rw [Finset.prod_singleton]`."
  rw [Finset.prod_singleton]

Conclusion
"
You verified that `∏ x ∈ {3}, x = 3`. The key lemma is
`Finset.prod_singleton`:

```
∏ x ∈ {a}, f x = f a
```

This is exactly the multiplicative analogue of `sum_singleton`:
a product over a single element is just that element.

## Sum vs. product: a comparison

| Operation | Notation | Identity | Type class |
|-----------|----------|----------|------------|
| Sum | `∑ x ∈ s, f x` | `0` | `AddCommMonoid` |
| Product | `∏ x ∈ s, f x` | `1` | `CommMonoid` |

The API mirrors `Finset.sum` almost exactly — every `sum_*` lemma has
a `prod_*` counterpart.

## What comes next

We will explore the product API: empty products, products over ranges,
and then move to algebraic manipulations that combine sums and products.
"

/-- `Finset.prod_singleton` states that `∏ x ∈ {a}, f x = f a`.

The product over a singleton finset equals the function applied to that
element. -/
TheoremDoc Finset.prod_singleton as "Finset.prod_singleton" in "Finset"

NewTheorem Finset.prod_singleton
DisabledTactic trivial decide native_decide simp aesop simp_all
