import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 7

Title "Changing the function inside a sum"

Introduction
"
# `Finset.sum_congr`: rewriting under the `∑`

Sometimes two sums are equal because the functions agree on every
element, even though they look syntactically different. For example,

$$\\sum_{i \\in s} (i + i) = \\sum_{i \\in s} 2i$$

because `i + i = 2 * i` for every `i`. The lemma `Finset.sum_congr`
lets you prove this:

```
Finset.sum_congr :
  s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum f = s₂.sum g
```

To use it, call `apply Finset.sum_congr rfl` (since the sets are the
same), which leaves you with `∀ x ∈ s, f x = g x`. Then introduce the
variable with `intro x _` and close the pointwise equality (often
with `ring`).

## Alternative: `congr 1` + `ext`

You can also use the `congr` tactic followed by `ext`:

```
congr 1    -- splits into two goals: s₁ = s₂ and f = g
ext x      -- changes f = g into ∀ x, f x = g x
ring       -- closes the pointwise equality
```

## Your task

Prove: `∑ i ∈ range n, (i + i) = ∑ i ∈ range n, (2 * i)`.
"

/-- Two sums are equal when the functions agree pointwise. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (i + i) = ∑ i ∈ Finset.range n, (2 * i) := by
  Hint "Use `apply Finset.sum_congr rfl` to reduce this to proving that
  `i + i = 2 * i` for every `i` in the range.

  Alternatively, use `congr 1` followed by `ext x` and `ring`."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`."
  apply Finset.sum_congr rfl
  Hint "Now the goal is `∀ x ∈ range n, x + x = 2 * x`.
  Introduce the variable with `intro x _` (the membership proof is
  not needed)."
  Hint (hidden := true) "Try `intro x _`."
  intro x _
  Hint "Now prove `x + x = 2 * x`. Use `ring`."
  Hint (hidden := true) "Use `ring`."
  ring

Conclusion
"
You proved that two sums with pointwise-equal functions are equal,
using `Finset.sum_congr`.

## When to use `sum_congr`

Use `sum_congr` when:
- Two sums range over the same set but the functions *look* different.
- You can prove they are *equal* pointwise (often by `ring` or `omega`).

This is common when you want to simplify or rearrange the expression
inside a big operator before applying other lemmas like `sum_add_distrib`
or `mul_sum`.

## The multiplicative analogue

`Finset.prod_congr` works identically for products:

```
Finset.prod_congr :
  s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.prod f = s₂.prod g
```

## What comes next

The boss level integrates everything: products, sums, algebraic
manipulation, and congr in a single proof.
"

/-- `Finset.sum_congr` states that if `s₁ = s₂` and `∀ x ∈ s₂, f x = g x`,
then `∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x`.

Use `apply Finset.sum_congr rfl` when the sets are the same and you
want to prove the functions agree pointwise. -/
TheoremDoc Finset.sum_congr as "Finset.sum_congr" in "Finset"

/-- `Finset.prod_congr` states that if `s₁ = s₂` and `∀ x ∈ s₂, f x = g x`,
then `∏ x ∈ s₁, f x = ∏ x ∈ s₂, g x`.

Use `apply Finset.prod_congr rfl` when the sets are the same and you
want to prove the functions agree pointwise. -/
TheoremDoc Finset.prod_congr as "Finset.prod_congr" in "Finset"

NewTheorem Finset.sum_congr Finset.prod_congr
DisabledTactic trivial decide native_decide simp aesop simp_all
