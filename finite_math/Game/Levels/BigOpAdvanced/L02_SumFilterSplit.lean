import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 2

Title "Splitting a sum into two parts"

Introduction
"
# `Finset.sum_filter_add_sum_filter_not`: the filter decomposition

Any sum over a finset can be split into two parts: the elements
satisfying a predicate, and those not satisfying it.

$$\\sum_{i \\in S} f(i) = \\sum_{\\substack{i \\in S \\\\ p(i)}} f(i) +
\\sum_{\\substack{i \\in S \\\\ \\neg p(i)}} f(i)$$

In Lean, this is `Finset.sum_filter_add_sum_filter_not`:

```
Finset.sum_filter_add_sum_filter_not (s : Finset ι) (p : ι → Prop)
  [DecidablePred p] (f : ι → M) :
  (∑ x ∈ s with p x, f x) + (∑ x ∈ s with ¬p x, f x) = ∑ x ∈ s, f x
```

The left-hand side has the split form (filter `p` + filter `¬p`),
and the right-hand side has the unified sum.

## Your task

Prove that the sum of the even-indexed elements plus the sum of the
odd-indexed elements equals the full sum.

Since the lemma's conclusion matches your goal exactly, you can close
it with `exact`.
"

/-- A sum splits into even-indexed and odd-indexed parts. -/
Statement (n : Nat) :
    (∑ i ∈ (Finset.range n).filter Even, i) +
    (∑ i ∈ (Finset.range n).filter (fun i => ¬ Even i), i) =
    ∑ i ∈ Finset.range n, i := by
  Hint "The goal is exactly the conclusion of
  `Finset.sum_filter_add_sum_filter_not` with `s = range n`,
  `p = Even`, and `f = id`.

  Try `exact Finset.sum_filter_add_sum_filter_not _ Even _`."
  Hint (hidden := true) "Try `exact Finset.sum_filter_add_sum_filter_not _ Even _`."
  exact Finset.sum_filter_add_sum_filter_not _ Even _

Conclusion
"
You split a sum into two complementary parts using
`sum_filter_add_sum_filter_not`.

## The splitting principle

This is one of the most useful identities in combinatorics. Whenever
you need to analyze a sum, splitting it by a well-chosen predicate
often simplifies each piece.

## Typical uses

- **Parity split**: sum of all = sum of evens + sum of odds
- **Threshold split**: sum over `{i | i ≤ k}` plus sum over `{i | i > k}`
- **Membership split**: sum over elements in a subset plus the rest

## In ordinary mathematics

On paper, you would write:
$$\\sum_{i=0}^{n-1} i = \\sum_{\\substack{0 \\le i < n \\\\ i \\text{ even}}} i
+ \\sum_{\\substack{0 \\le i < n \\\\ i \\text{ odd}}} i$$

and consider this obvious. In Lean, `sum_filter_add_sum_filter_not`
makes this reasoning explicit.

## What comes next

The next level uses `sum_range_add` to split a range sum differently:
by splitting the index range itself.
"

/-- `Finset.sum_filter_add_sum_filter_not` states that
`(∑ x ∈ s with p x, f x) + (∑ x ∈ s with ¬p x, f x) = ∑ x ∈ s, f x`.

A sum splits into the part satisfying `p` plus the part not satisfying `p`. -/
TheoremDoc Finset.sum_filter_add_sum_filter_not as "Finset.sum_filter_add_sum_filter_not" in "Finset"

NewTheorem Finset.sum_filter_add_sum_filter_not
DisabledTactic trivial decide native_decide simp aesop simp_all
