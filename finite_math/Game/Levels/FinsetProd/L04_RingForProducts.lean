import GameServer.Commands
import Mathlib

World "FinsetProd"
Level 4

Title "Using ring with products"

Introduction
"
# Algebraic manipulation with `ring`

You have used `ring` in earlier worlds to close arithmetic equalities.
In this level you will combine `prod_range_succ` with `ring` to prove
a product identity by induction.

## The statement

Prove by induction:
$$\\prod_{i=0}^{n-1} 2 = 2^n$$

In Lean: `∏ i ∈ range n, 2 = 2 ^ n`.

## Strategy

1. `induction n with`
2. Base case: `range 0 = ∅`, so the product is `1`. And `2 ^ 0 = 1`.
   Use `rfl`.
3. Inductive step:
   - `rw [Finset.prod_range_succ, ih]` — peel off the last `2` and
     apply the hypothesis.
   - `ring` closes `2 ^ n * 2 = 2 ^ (n + 1)`.
"

/-- The product of `n` twos is `2 ^ n`. -/
Statement (n : Nat) : ∏ i ∈ Finset.range n, (2 : Nat) = 2 ^ n := by
  Hint "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Peel off the last factor and apply the inductive hypothesis:
    `rw [Finset.prod_range_succ, ih]`.
    Then close the algebra with `ring`."
    Hint (hidden := true) "Try `rw [Finset.prod_range_succ, ih]` followed by `ring`."
    rw [Finset.prod_range_succ, ih]
    Hint "The goal is now `2 ^ n * 2 = 2 ^ (n + 1)`. Use `ring` to
    close it."
    Hint (hidden := true) "Use `ring`."
    ring

Conclusion
"
You proved `∏ i ∈ range n, 2 = 2 ^ n` by induction — the multiplicative
analogue of `∑ i ∈ range n, 2 = 2 * n`.

## The multiplicative induction template

The pattern is identical to inductive sum proofs:

1. `induction n with`
2. Base case: `rfl`
3. Inductive step: `rw [prod_range_succ, ih]`, then `ring`

The only difference is that you use `prod_range_succ` instead of
`sum_range_succ`, and the algebra involves `*` and `^` instead of `+`
and `*`.

## What comes next

Now that you are comfortable with products, the next levels explore
algebraic manipulation *inside* big-operator expressions — distributing
sums, pulling out constants, and changing the function inside a sum or
product.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
