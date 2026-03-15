import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 3

Title "Splitting a range sum"

Introduction
"
# `Finset.sum_range_add`: splitting by range

Filter decomposition splits by a *predicate*. There is another way to
split: by dividing the *index range* itself.

The lemma `Finset.sum_range_add` says:

```
Finset.sum_range_add (f : ℕ → M) (n m : ℕ) :
  ∑ x ∈ range (n + m), f x =
  (∑ x ∈ range n, f x) + ∑ x ∈ range m, f (n + x)
```

This decomposes `range (n + m)` into the first `n` terms and the
remaining `m` terms — but the remaining terms are **reindexed**: the
index `x` in the second sum ranges from `0` to `m - 1`, and the
function is evaluated at `f (n + x)`.

## Your task

Prove:
$$\\sum_{i=0}^{n+m-1} i^2 = \\left(\\sum_{i=0}^{n-1} i^2\\right) +
\\sum_{i=0}^{m-1} (n + i)^2$$

Use `exact Finset.sum_range_add _ n m` or `rw [Finset.sum_range_add]`.
"

/-- Splitting a range sum using `sum_range_add`. -/
Statement (n m : Nat) :
    ∑ i ∈ Finset.range (n + m), i ^ 2 =
    (∑ i ∈ Finset.range n, i ^ 2) + ∑ i ∈ Finset.range m, (n + i) ^ 2 := by
  Hint "Use `Finset.sum_range_add` to split the sum over `range (n + m)`
  into two parts.

  Try `exact Finset.sum_range_add _ n m` or `rw [Finset.sum_range_add]`."
  Hint (hidden := true) "Try `exact Finset.sum_range_add (· ^ 2) n m`."
  exact Finset.sum_range_add (· ^ 2) n m

Conclusion
"
You used `sum_range_add` to split a range into two consecutive
subranges.

## Filter split vs. range split

You now know two ways to decompose a sum:

| Method | What it splits | Key lemma |
|--------|---------------|-----------|
| **Filter** | By predicate on elements | `sum_filter_add_sum_filter_not` |
| **Range** | By dividing the index range | `sum_range_add` |

The filter split is more general (works on any finset), while the
range split is specific to `range` but produces a cleaner result when
you are working with consecutive indices.

## The reindexing

Notice that `sum_range_add` automatically reindexes the second sum:
the index runs from `0` to `m - 1`, and the function sees `n + x`
instead of the original indices `n, n+1, ..., n+m-1`. This is a
simple example of **reindexing** — we will see more general versions
later in this world.

## What comes next

The next level introduces `Finset.sum_comm` for interchanging the
order of a double sum.
"

/-- `Finset.sum_range_add` states that
`∑ x ∈ range (n + m), f x = (∑ x ∈ range n, f x) + ∑ x ∈ range m, f (n + x)`.

A range sum splits into two consecutive subrange sums. -/
TheoremDoc Finset.sum_range_add as "Finset.sum_range_add" in "Finset"

NewTheorem Finset.sum_range_add
DisabledTactic trivial decide native_decide simp aesop simp_all
