import Game.Metadata

World "BigOpAlgebra"
Level 8

Title "Interchanging Double Sums"

Introduction "
# Double Sums: Swapping the Order

When you have a double sum — a sum inside a sum — you can swap
the order of summation:

$$\\sum_{x \\in s} \\sum_{y \\in t} f(x, y) = \\sum_{y \\in t} \\sum_{x \\in s} f(x, y)$$

This is `Finset.sum_comm`:
```
Finset.sum_comm :
  ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
```

This is the finite analogue of Fubini's theorem from analysis.
For finite sums, it always holds — no convergence conditions
needed.

**Why it matters**: Many counting and algebraic arguments become
easier when you sum in a different order. A problem that looks
hard when summing over `x` first might become trivial when you
sum over `y` first.

**Your task**: Given the sum in one order, deduce it in the other.
"

/-- Swap the order of a double sum. -/
Statement (s t : Finset ℕ) (f : ℕ → ℕ → ℕ)
    (h : ∑ y ∈ t, ∑ x ∈ s, f x y = 100) :
    ∑ x ∈ s, ∑ y ∈ t, f x y = 100 := by
  Hint "Use `rw [Finset.sum_comm]` to swap the summation order."
  rw [Finset.sum_comm]
  Hint "The goal now matches hypothesis `h`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`sum_comm` is a workhorse in combinatorics and algebra. Whenever
you see a double sum and the current summation order is
inconvenient, consider swapping.

**The grid picture**: Think of `f(x, y)` as values in a
rectangular grid with rows indexed by `s` and columns by `t`.
Summing by rows first means: for each row `x`, add up the
column entries, then add the row totals. Summing by columns
first means: for each column `y`, add up the row entries, then
add the column totals. Either way you add every cell exactly
once, so the grand total is the same. This is why `sum_comm`
works — and it's the combinatorial insight behind double
counting arguments throughout mathematics.

**No conditions needed**: Unlike the continuous case (where
Fubini's theorem requires absolute convergence), finite sum
interchange is always valid.
"

/-- `Finset.sum_comm` states that
`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`.

The order of summation in a double sum can be freely interchanged.

## Syntax
```
exact Finset.sum_comm
rw [Finset.sum_comm]
```

## When to use it
When you have a double sum `∑ x, ∑ y, ...` and want to swap to
`∑ y, ∑ x, ...`.

## Warning
`sum_comm` swaps **all** nesting levels at once. If you have
triple sums, you may need to apply it more carefully.
-/
TheoremDoc Finset.sum_comm as "Finset.sum_comm" in "BigOp"

NewTheorem Finset.sum_comm

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
