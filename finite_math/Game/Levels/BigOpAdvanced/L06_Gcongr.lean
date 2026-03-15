import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 6

Title "Introducing gcongr"

Introduction
"
# The `gcongr` tactic: monotone inequality goals

So far, all our big-operator goals have been **equalities**. But in
mathematics, we often need **inequalities** between sums:

$$\\text{If } f(i) \\le g(i) \\text{ for all } i \\in S, \\text{ then }
\\sum_{i \\in S} f(i) \\le \\sum_{i \\in S} g(i).$$

The tactic **`gcongr`** (\"generalized congruence\") handles this
automatically. When your goal is an inequality between sums (or
products, or other monotone operations), `gcongr` reduces it to a
pointwise inequality.

## How `gcongr` works

If your goal is:
```
∑ i ∈ s, f i ≤ ∑ i ∈ s, g i
```

Then `gcongr with i hi` produces:
```
i : ι
hi : i ∈ s
⊢ f i ≤ g i
```

It automatically applies the monotonicity lemma for `∑` and leaves
you with the pointwise obligation.

## Your task

Prove: if `f i ≤ g i` for all `i ∈ range n`, then `∑ f ≤ ∑ g`.

Use `gcongr with i hi` to reduce the sum inequality to a pointwise
inequality, then use the hypothesis `h`.
"

/-- Use `gcongr` to reduce a sum inequality to pointwise. -/
Statement (n : Nat) (f g : Nat → Nat)
    (h : ∀ i ∈ Finset.range n, f i ≤ g i) :
    ∑ i ∈ Finset.range n, f i ≤ ∑ i ∈ Finset.range n, g i := by
  Hint "The goal is an inequality between two sums with the same index
  set. Use `gcongr with i hi` to reduce it to a pointwise inequality.

  This will give you a goal `f i ≤ g i` with the hypothesis `i ∈ range n`."
  Hint (hidden := true) "Try `gcongr with i hi`."
  gcongr with i hi
  Hint "Now apply the hypothesis `h` to get the pointwise inequality.
  Use `exact h i hi`."
  Hint (hidden := true) "Try `exact h i hi`."
  exact h i hi

Conclusion
"
You used `gcongr` to reduce a sum inequality to a pointwise inequality!

## When to use `gcongr`

Use `gcongr` when:
- The goal is an inequality between sums, products, or other monotone
  operations.
- Both sides have the same \"shape\" (same index set, same outer
  operation), differing only in the inner function.

## What `gcongr` knows

`gcongr` has built-in knowledge of monotonicity for many operations:
- Sums: `∑ f ≤ ∑ g` from `f ≤ g` pointwise
- Addition: `a + b ≤ c + d` from `a ≤ c` and `b ≤ d`
- Multiplication (by nonneg): `a * b ≤ c * d` from `a ≤ c`, `b ≤ d`
- Powers, absolute values, norms, and more

## Transfer

In ordinary mathematics, the statement \"if each term is smaller, the
sum is smaller\" is intuitive. In Lean, `gcongr` is the tactic that
makes this reasoning automatic.

## What comes next

The next level introduces **reindexing**: changing the index variable
of a sum.
"

/-- The `gcongr` tactic proves goals involving monotone operations
(sums, products, addition, etc.) by reducing them to pointwise or
component-wise subgoals.

For sum inequalities, use `gcongr with i hi` to reduce
`∑ i ∈ s, f i ≤ ∑ i ∈ s, g i` to `f i ≤ g i`. -/
TacticDoc gcongr

NewTactic gcongr
DisabledTactic trivial decide native_decide simp aesop simp_all
