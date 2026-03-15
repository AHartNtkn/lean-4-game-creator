import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 6

Title "Sum of the first n odd numbers"

Introduction
"
# A classic identity: the sum of odd numbers

Here is one of the most beautiful identities in elementary mathematics:

$$1 + 3 + 5 + \\cdots + (2n-1) = n^2$$

In our notation, this becomes:

$$\\sum_{i=0}^{n-1} (2i + 1) = n^2$$

The $i$-th odd number (starting from $i = 0$) is $2i + 1$: when $i = 0$
we get $1$, when $i = 1$ we get $3$, when $i = 2$ we get $5$, and so on.

## Strategy

The proof follows the same induction template:

1. Base case: both sides are `0`. `rfl`.
2. Inductive step: apply `sum_range_succ` and `ih`, then use `ring`
   to verify `n^2 + (2n + 1) = (n+1)^2`.

This is the first identity where the function depends on `i`.
"

/-- The sum of the first `n` odd numbers is `n^2`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  Hint "The pattern is the same: `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Peel off the last term and apply `ih`:
    `rw [Finset.sum_range_succ, ih]`.
    This leaves `n ^ 2 + (2 * n + 1) = (n + 1) ^ 2`."
    rw [Finset.sum_range_succ, ih]
    Hint "The goal is `n ^ 2 + (2 * n + 1) = (n + 1) ^ 2`.
    This is a polynomial equality — `ring` closes it."
    Hint (hidden := true) "Use `ring`."
    ring

Conclusion
"
You proved the classic identity: the sum of the first $n$ odd numbers
is $n^2$.

## Why this works

The algebraic core of the inductive step is the identity
$$n^2 + (2n + 1) = (n + 1)^2$$
which is just the expansion of a perfect square. The `ring` tactic
verifies this automatically.

## A geometric interpretation

This identity has a beautiful geometric proof: arrange unit squares
in an L-shape (a \"gnomon\") around the previous square. The $n$-th
gnomon has $2n + 1$ squares, and together they build an $(n+1) \\times
(n+1)$ square. Our inductive proof captures exactly this step.

## Checkpoint

You have now seen the full induction-on-range-sums pattern with a
non-trivial function. The next levels will deepen your control of this
technique.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
