import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 9

Title "Boss: Double sum decomposition"

Introduction
"
# Boss: Decompose a double sum

Time to put everything together. You will prove an identity that
requires multiple techniques from this world.

## The statement

Prove:
$$\\sum_{i=0}^{n-1}\\sum_{j=0}^{m-1}(i + j)
\\;=\\; m\\cdot\\sum_{i=0}^{n-1} i \\;+\\; n\\cdot\\sum_{j=0}^{m-1} j$$

## Strategy

This proof uses four moves:

1. **`conv` + `sum_add_distrib`** (L5 + W15): Use `conv` to enter the
   outer sum, then distribute the inner sum of `(i + j)` into
   `(∑ j, i) + (∑ j, j)`.

2. **`sum_add_distrib`** (W15): Distribute the outer sum across the
   two inner pieces.

3. **`conv` + `sum_const` + `card_range`** (L5 + W15): The inner sum
   `∑ j ∈ range m, i` is a constant sum equal to `m * i`. Use `conv`
   to rewrite it, then `← mul_sum` to factor out `m`.

4. **`sum_const` + `card_range`** (W15): The outer sum of a constant
   inner sum `∑ i ∈ range n, (∑ j ∈ range m, j)` equals
   `n * (∑ j ∈ range m, j)`.
"

/-- A double sum decomposed into two single sums. -/
Statement (n m : Nat) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, (i + j) =
    m * (∑ i ∈ Finset.range n, i) + n * (∑ j ∈ Finset.range m, j) := by
  Hint "Start by using `conv` to rewrite inside the outer sum. Enter
  the outer sum's function with `conv_lhs => arg 2; ext i`, then
  apply `sum_add_distrib` to split the inner sum `∑ j, (i + j)` into
  `(∑ j, i) + (∑ j, j)`.

  ```
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_add_distrib]
  ```"
  Hint (hidden := true) "Try:
  ```
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_add_distrib]
  ```"
  conv_lhs =>
    arg 2
    ext i
    rw [Finset.sum_add_distrib]
  Hint "Good! Now the goal is:
  ```
  ∑ i ∈ range n, ((∑ j ∈ range m, i) + ∑ j ∈ range m, j) = ...
  ```

  Distribute the outer sum using `rw [Finset.sum_add_distrib]`."
  Hint (hidden := true) "Try `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "Now the goal is:
  ```
  (∑ i ∈ range n, ∑ j ∈ range m, i) +
  (∑ i ∈ range n, ∑ j ∈ range m, j) = m * ... + n * ...
  ```

  Use `congr 1` to split into two subgoals: one for each summand."
  Hint (hidden := true) "Try `congr 1`."
  congr 1
  · Hint "Goal: `∑ i ∈ range n, ∑ j ∈ range m, i = m * ∑ i ∈ range n, i`.

    The inner sum `∑ j ∈ range m, i` sums a constant `i` over `m`
    terms, so it equals `m * i`.

    Use `conv` to rewrite `∑ j ∈ range m, i` to `m * i`:
    ```
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ```"
    Hint (hidden := true) "Try:
    ```
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    ```"
    conv_lhs =>
      arg 2
      ext i
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
    Hint "Now the goal is `∑ i ∈ range n, m * i = m * ∑ i ∈ range n, i`.

    Pull the constant `m` out of the sum using `← Finset.mul_sum`."
    Hint (hidden := true) "Try `rw [← Finset.mul_sum]`."
    rw [← Finset.mul_sum]
  · Hint "Goal: `∑ i ∈ range n, ∑ j ∈ range m, j = n * ∑ j ∈ range m, j`.

    The summand `∑ j ∈ range m, j` does not depend on `i`, so the outer
    sum repeats the same value `n` times.

    Use `Finset.sum_const` and `Finset.card_range` to collapse it:
    `rw [Finset.sum_const, Finset.card_range, smul_eq_mul]`."
    Hint (hidden := true) "Try `rw [Finset.sum_const, Finset.card_range, smul_eq_mul]`."
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

Conclusion
"
Congratulations on completing the **advanced big-operator** world!

You decomposed a double sum into two separate single sums by:

1. **`conv` + `sum_add_distrib`** — split the inner sum inside the binder
2. **`sum_add_distrib`** — split the outer sum
3. **`conv` + `sum_const` + `card_range` + `mul_sum`** — collapsed the
   constant inner sum and factored out `m`
4. **`sum_const` + `card_range`** — collapsed the repeated outer sum

## What you learned in this world

| Level | Key lesson |
|-------|-----------|
| L01 | `sum_filter` — filtering converts to a conditional |
| L02 | `sum_filter_add_sum_filter_not` — split by predicate |
| L03 | `sum_range_add` — split a range into subranges |
| L04 | `sum_comm` — interchange summation order |
| L05 | `conv` — rewrite inside a binder |
| L06 | `gcongr` — reduce monotone inequalities pointwise |
| L07 | `sum_nbij'` — reindex via an explicit bijection |
| L08 | Reindexing practice + `sum_equiv` |
| L09 | Boss — integrate everything in a double-sum decomposition |

## Transfer

In ordinary mathematics, you would write:

> $$\\sum_{i=0}^{n-1}\\sum_{j=0}^{m-1}(i+j)
> = \\sum_i \\left(\\sum_j i + \\sum_j j\\right)
> = \\sum_i m\\cdot i + \\sum_i \\sum_j j
> = m \\sum_i i + n \\sum_j j$$

Each step is \"obvious\" on paper. In Lean, each corresponds to a
specific lemma or technique: `sum_add_distrib` for splitting,
`sum_const` for constant sums, `mul_sum` for factoring, and `conv` for
reaching inside the binder. The `conv` steps are uniquely Lean — they
correspond to the implicit \"rewriting each term\" steps that you
never write on paper.

## What comes next

The next world provides a problem set to practice these advanced
big-operator techniques on fresh surface forms.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
