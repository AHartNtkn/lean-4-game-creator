import GameServer.Commands
import Mathlib

World "Factorials"
Level 3

Title "Factorial as a big product"

Introduction
"
# Connecting factorials to big products

There is a deep connection between factorials and the `∏` notation
you learned in the **Finset.prod** world:

$$n! = \\prod_{i=0}^{n-1} (i + 1) = 1 \\cdot 2 \\cdot 3 \\cdots n$$

In Lean: `Nat.factorial n = ∏ i ∈ Finset.range n, (i + 1)`.

## Your task

Verify this connection for the concrete case $n = 4$:

$$\\prod_{i=0}^{3} (i + 1) = 4!$$

## Strategy

Unfold both sides to numeric values. On the left, use
`Finset.prod_range_succ` repeatedly to peel off factors. On the right,
use `Nat.factorial_succ` repeatedly. Then `ring` closes the resulting
arithmetic equality.
"

/-- The product 1 * 2 * 3 * 4 equals 4!. -/
Statement : ∏ i ∈ Finset.range 4, (i + 1) = Nat.factorial 4 := by
  Hint "Unfold the product on the left by applying `Finset.prod_range_succ`
  four times, then `Finset.prod_range_zero`.

  Try `rw [Finset.prod_range_succ]` to peel off the last factor."
  Hint (hidden := true) "Try:
  ```
  rw [Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero]
  ```"
  rw [Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_succ, Finset.prod_range_succ,
      Finset.prod_range_zero]
  Hint "Now unfold the factorial on the right using `Nat.factorial_succ`
  four times, then `Nat.factorial_zero`."
  Hint (hidden := true) "Try:
  ```
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_zero]
  ```"
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_zero]
  Hint "Both sides are now numeric expressions that differ only in
  grouping and order. Use `ring` to close the goal."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion
"
You verified that $\\prod_{i=0}^{3}(i+1) = 4!$ by unfolding both sides.

## The general identity

The fact that $n! = \\prod_{i=0}^{n-1}(i+1)$ holds for all $n$.
In Lean, this is `Nat.factorial_eq_prod_range_add_one`:

```
Nat.factorial_eq_prod_range_add_one (n : ℕ) :
  Nat.factorial n = ∏ i ∈ Finset.range n, (i + 1)
```

You will prove this general identity as the boss of this world.

## Transfer moment

In ordinary mathematics, the identity $n! = 1 \\cdot 2 \\cdots n$
is the *definition*. In Lean, the definition is recursive:
$0! = 1$, $(n+1)! = (n+1) \\cdot n!$. The identity
$n! = \\prod_{i=0}^{n-1}(i+1)$ is a *theorem* that must be proved
by induction — connecting the recursive definition to the product
formula.

## What comes next

The next level introduces descending factorials.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
