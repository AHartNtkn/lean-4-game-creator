import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 7

Title "Computing a concrete sum"

Introduction
"
# Step-by-step computation of a concrete sum

Let's evaluate `∑ x ∈ {1, 2, 3}, x ^ 2` by hand, using the lemmas
you've learned.

## The plan

The finset `{1, 2, 3}` is really `insert 1 (insert 2 {3})`. So:

1. `sum_insert` on the outer `insert 1 ...` gives:
   `1 ^ 2 + ∑ x ∈ {2, 3}, x ^ 2`

2. `sum_insert` on `insert 2 {3}` gives:
   `1 ^ 2 + (2 ^ 2 + ∑ x ∈ {3}, x ^ 2)`

3. `sum_singleton` on `{3}` gives:
   `1 ^ 2 + (2 ^ 2 + 3 ^ 2)`

4. Arithmetic: `1 + 4 + 9 = 14`.

## Membership proofs

To use `sum_insert`, you need `a ∉ s`. For concrete numbers, these
are simple: `1 ∉ {2, 3}` and `2 ∉ {3}`. We can prove these inline
with `norm_num`.
"

/-- Evaluate `∑ x ∈ {1, 2, 3}, x ^ 2` step by step. -/
Statement : ∑ x ∈ ({1, 2, 3} : Finset Nat), (x ^ 2) = 14 := by
  Hint "The finset is `insert 1 (insert 2 (singleton 3))`.
  Use `rw [Finset.sum_insert]` to peel off the first element.

  You need a proof that `1` is not in the remaining set. Try:
  `have h1 : (1 : Nat) ∉ (insert 2 (singleton 3) : Finset Nat) := by norm_num`
  then `rw [Finset.sum_insert h1]`."
  have h1 : (1 : Nat) ∉ ({2, 3} : Finset Nat) := by norm_num
  rw [Finset.sum_insert h1]
  Hint "Now peel off `2` with another `sum_insert`.
  Establish `2 ∉ (singleton 3)`, then rewrite."
  Hint (hidden := true) "Use
  `have h2 : (2 : Nat) ∉ (singleton 3 : Finset Nat) := by norm_num`
  then `rw [Finset.sum_insert h2]`."
  have h2 : (2 : Nat) ∉ ({3} : Finset Nat) := by norm_num
  rw [Finset.sum_insert h2]
  Hint "Now use `rw [Finset.sum_singleton]` to handle the last element."
  rw [Finset.sum_singleton]
  Hint "The goal is now arithmetic. Close with `norm_num`."
  Hint (hidden := true) "Use `norm_num`."
  norm_num

Conclusion
"
You computed `∑ x ∈ {1, 2, 3}, x ^ 2 = 14` by repeatedly applying
`sum_insert` and `sum_singleton`, then evaluating the arithmetic.

## The decomposition pattern

For any concrete finset, you can compute the sum by:
1. Repeated `sum_insert` to peel off each element
2. `sum_singleton` for the last element
3. Arithmetic to evaluate the result

This is tedious by hand, but it shows what `Finset.sum` actually means:
it really does add up the function values over the elements.

## Automation note

In practice, `simp` with appropriate lemmas can do all of this automatically.
But in this course, we keep `simp` disabled so you can see the mechanics.
"

DisabledTactic trivial decide native_decide simp aesop simp_all norm_num
