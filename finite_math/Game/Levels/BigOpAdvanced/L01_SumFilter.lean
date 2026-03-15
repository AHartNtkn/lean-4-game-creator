import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 1

Title "Splitting a sum by filtering"

Introduction
"
# `Finset.sum_filter`: splitting a sum by a predicate

Welcome to the **advanced big-operator** world! You already know how to
take sums over finsets using `∑`, and you know basic algebraic
manipulations like `sum_add_distrib` and `mul_sum`. This world teaches
you three powerful new skills:

1. **Filtering and splitting** — decomposing a sum according to a
   predicate.
2. **`conv` and `gcongr`** — two new tactics for rewriting inside
   binders and for monotone inequality goals.
3. **Reindexing** — changing the index variable of a sum.

## Filtering

The lemma `Finset.sum_filter` relates a sum over a filtered set to
a sum with an `if`-`then`-`else`:

```
Finset.sum_filter (p : ι → Prop) [DecidablePred p] (f : ι → M) :
  ∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0
```

Here `s with p a` means the elements of `s` satisfying `p`. The
right-hand side replaces filtering with a conditional: elements
satisfying `p` contribute `f a`, others contribute `0`.

## Your task

Prove that summing squares over even numbers in `range n` equals
summing `if Even i then i ^ 2 else 0` over all of `range n`.

Use `rw [Finset.sum_filter]`.
"

/-- Filtering a sum replaces the filter with a conditional. -/
Statement (n : Nat) :
    ∑ i ∈ (Finset.range n).filter Even, i ^ 2 =
    ∑ i ∈ Finset.range n, if Even i then i ^ 2 else 0 := by
  Hint "The lemma `Finset.sum_filter` converts a sum over a filtered
  set into a conditional sum. Use `rw [Finset.sum_filter]` to rewrite
  the left-hand side."
  Hint (hidden := true) "Try `rw [Finset.sum_filter]`."
  rw [Finset.sum_filter]

Conclusion
"
You used `Finset.sum_filter` to convert a sum over a filtered finset
into a sum with a conditional.

## The connection

Filtering is conceptually natural: \"sum only the elements satisfying
`p`.\" The conditional form is computationally equivalent: \"sum
everything, but zero out the elements not satisfying `p`.\" The lemma
`sum_filter` lets you switch between these two views.

## In ordinary mathematics

On paper, you might write:
$$\\sum_{\\substack{i \\in S \\\\ p(i)}} f(i) = \\sum_{i \\in S}
\\begin{cases} f(i) & \\text{if } p(i) \\\\ 0 & \\text{otherwise} \\end{cases}$$

This is exactly what `sum_filter` formalizes.

## What comes next

The next level uses filter decomposition to split a sum into two parts.
"

/-- `Finset.sum_filter` states that
`∑ a ∈ s with p a, f a = ∑ a ∈ s, if p a then f a else 0`.

A sum over a filtered set equals a conditional sum over the original set. -/
TheoremDoc Finset.sum_filter as "Finset.sum_filter" in "Finset"

NewTheorem Finset.sum_filter
DisabledTactic trivial decide native_decide simp aesop simp_all
