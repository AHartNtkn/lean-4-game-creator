import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 6

Title "Pulling a constant out of a sum"

Introduction
"
# `Finset.mul_sum`: extracting a constant factor

In ordinary algebra, you can factor out a constant:
$$\\sum_{i=0}^{n-1} c \\cdot f(i) = c \\cdot \\sum_{i=0}^{n-1} f(i).$$

In Lean, this is `Finset.mul_sum`:

```
Finset.mul_sum (s : Finset ι) (f : ι → R) (a : R) :
  a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i
```

Note the direction: `mul_sum` rewrites `a * ∑ f` into `∑ (a * f)`.
If your goal has `∑ (a * f)` on the left, use `← Finset.mul_sum` to
pull the constant out.

There is also `Finset.sum_mul` for the right side:
```
Finset.sum_mul (s : Finset ι) (f : ι → R) (a : R) :
  (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a
```

## Your task

Prove: `∑ i ∈ range n, (3 * i) = 3 * (∑ i ∈ range n, i)`.

Since the goal has `∑ (3 * ·)` on the left and `3 * ∑` on the right,
use `← Finset.mul_sum` on the right side (or `Finset.mul_sum` to rewrite
the right into the left).
"

/-- Pulling a constant factor out of a sum. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (3 * i) = 3 * (∑ i ∈ Finset.range n, i) := by
  Hint "The right-hand side has `3 * ∑ ...`. Use `Finset.mul_sum` to
  rewrite it into `∑ (3 * ·)`, matching the left-hand side.

  Try `rw [Finset.mul_sum]`."
  Hint (hidden := true) "Try `rw [Finset.mul_sum]`."
  rw [Finset.mul_sum]

Conclusion
"
You pulled a constant factor out of a sum using `mul_sum`.

## The two directions

- `Finset.mul_sum`: `a * ∑ f = ∑ (a * f)`
- `Finset.sum_mul`: `(∑ f) * a = ∑ (f * a)`

These are the additive-sum analogues of distributivity. In practice,
you often use `← mul_sum` to factor out a constant from a sum, and
`mul_sum` to distribute a constant into a sum.

## When to use which

- Goal has `∑ (c * f)` and you want `c * ∑ f`: use `← mul_sum`
- Goal has `c * ∑ f` and you want `∑ (c * f)`: use `mul_sum`
- Constant on the right? Replace `mul_sum` with `sum_mul`

## What comes next

The next level introduces `Finset.sum_congr` — changing the function
inside a sum or product.
"

/-- `Finset.mul_sum` states that `a * ∑ i ∈ s, f i = ∑ i ∈ s, a * f i`.

Distributes a constant factor into a sum. Use `← Finset.mul_sum` to
pull a constant out of a sum. -/
TheoremDoc Finset.mul_sum as "Finset.mul_sum" in "Finset"

/-- `Finset.sum_mul` states that `(∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a`.

Distributes a constant factor (on the right) into a sum. Use
`← Finset.sum_mul` to pull a constant out of a sum. -/
TheoremDoc Finset.sum_mul as "Finset.sum_mul" in "Finset"

NewTheorem Finset.mul_sum Finset.sum_mul
DisabledTactic trivial decide native_decide simp aesop simp_all
