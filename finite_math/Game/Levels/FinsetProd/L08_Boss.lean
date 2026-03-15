import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 8

Title "Boss: Algebraic big-operator identity"

Introduction
"
# Boss: Decompose a big-operator expression

Time to integrate everything you have learned in this world.

## The statement

Prove:
$$\\sum_{i=0}^{n-1} (3i + i^2) \\;=\\; 3 \\cdot \\sum_{i=0}^{n-1} i \\;+\\; \\sum_{i=0}^{n-1} i^2$$

In Lean:
```
∑ i ∈ range n, (3 * i + i * i) = 3 * (∑ i ∈ range n, i) + ∑ i ∈ range n, i ^ 2
```

## Strategy

This requires three moves from this world:

1. **`sum_congr`**: The left-hand side has `i * i` but the right has
   `i ^ 2`. Use `Finset.sum_congr rfl` with a pointwise proof
   (via `ring`) to normalize `i * i` to `i ^ 2`.

2. **`sum_add_distrib`**: After the congr step, split
   `∑ (3i + i²)` into `(∑ 3i) + (∑ i²)`.

3. **`← mul_sum`**: Pull the constant `3` out of `∑ 3i` to get
   `3 * (∑ i)`.

Each step uses a different algebraic manipulation lemma from this
world.
"

/-- A big-operator identity requiring congr, distrib, and constant extraction. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (3 * i + i * i) =
    3 * (∑ i ∈ Finset.range n, i) + ∑ i ∈ Finset.range n, i ^ 2 := by
  Hint "Start by normalizing the function inside the sum. The left-hand
  side has `i * i` but the right-hand side has `i ^ 2`. Use
  `Finset.sum_congr rfl` to change `3 * i + i * i` to `3 * i + i ^ 2`.

  First, prove the pointwise equality:
  `have h : ∀ x ∈ Finset.range n, 3 * x + x * x = 3 * x + x ^ 2 := by intro x _; ring`
  Then `rw [Finset.sum_congr rfl h]`."
  Hint (hidden := true) "Try:
  ```
  have h : ∀ x ∈ Finset.range n, 3 * x + x * x = 3 * x + x ^ 2 := by intro x _; ring
  rw [Finset.sum_congr rfl h]
  ```"
  have hcongr : ∀ x ∈ Finset.range n, 3 * x + x * x = 3 * x + x ^ 2 := by
    intro x _; ring
  rw [Finset.sum_congr rfl hcongr]
  Hint "Now the goal is:
  `∑ i ∈ range n, (3 * i + i ^ 2) = 3 * (∑ i ∈ range n, i) + ∑ i ∈ range n, i ^ 2`

  Split the left-hand sum using `Finset.sum_add_distrib`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now the goal is:
  `(∑ i ∈ range n, 3 * i) + (∑ i ∈ range n, i ^ 2) = 3 * (∑ i ∈ range n, i) + ...`

  Pull the constant `3` out of the first sum using `← Finset.mul_sum`."
  Hint (hidden := true) "Try `rw [← Finset.mul_sum]`."
  rw [← Finset.mul_sum]

Conclusion
"
Congratulations on completing the **Finset.prod** world!

You decomposed a sum of a mixed expression into structured parts:

1. **`sum_congr`** — normalized `i * i` to `i ^ 2` inside the sum
2. **`sum_add_distrib`** — split `∑ (f + g)` into `∑ f + ∑ g`
3. **`← mul_sum`** — pulled the constant `3` out of `∑ (3 * ·)`

## What you learned in this world

- **L01**: `Finset.prod` — big products and `prod_singleton`
- **L02**: `prod_empty` — the empty product is `1`
- **L03**: `prod_range_succ` — peeling off the last factor
- **L04**: Inductive product proof with `ring`
- **L05**: `sum_add_distrib` — splitting sums of sums
- **L06**: `mul_sum` / `sum_mul` — extracting constant factors
- **L07**: `sum_congr` / `prod_congr` — changing the function inside a big operator
- **L08**: Boss — integrating all manipulation techniques

## Transfer moment

In ordinary mathematics, you would write:

> $\\sum_{i=0}^{n-1}(3i + i^2) = \\sum_{i=0}^{n-1} 3i + \\sum_{i=0}^{n-1} i^2
>  = 3\\sum_{i=0}^{n-1} i + \\sum_{i=0}^{n-1} i^2$

Each equality is \"obvious\" on paper — you just rearrange terms. In Lean, each
step corresponds to a specific lemma: `sum_add_distrib` for splitting and
`mul_sum` for factoring. The `sum_congr` step (normalizing `i \\cdot i`
to $i^2$) is something you would never write on paper but need in Lean
because syntax matters.

**In plain language**: To manipulate expressions inside big operators,
split sums with `sum_add_distrib`, extract constants with `mul_sum`,
and normalize the function with `sum_congr`.

## What comes next

The next world introduces **splitting, filtering, and reindexing** —
more advanced operations on big-operator expressions.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
