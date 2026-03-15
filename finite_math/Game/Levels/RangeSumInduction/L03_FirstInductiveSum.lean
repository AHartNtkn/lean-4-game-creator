import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 3

Title "First inductive sum"

Introduction
"
# First inductive sum proof

Time to combine `induction` with `sum_range_succ`.

## The statement

Prove: for all `n`, `∑ i ∈ range n, 1 = n`.

In words: the sum of `n` ones is `n`.

## The proof structure

```
induction n with
| zero => ...        -- base case: sum over range 0 is 0
| succ n ih => ...   -- inductive step: peel off the last 1
```

**Base case**: `∑ i ∈ range 0, 1 = 0`. Since `range 0 = ∅`, this
reduces to `0 = 0`, which is `rfl`.

**Inductive step**: Assume `∑ i ∈ range n, 1 = n` (this is `ih`).
Prove `∑ i ∈ range (n+1), 1 = n + 1`.
Use `rw [Finset.sum_range_succ]` to get
`(∑ i ∈ range n, 1) + 1 = n + 1`,
then `rw [ih]` to finish.
"

/-- The sum of `n` ones is `n`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 1 = n := by
  Hint "Start with `induction n with` to split into base case and
  inductive step."
  induction n with
  | zero =>
    Hint "The base case: `∑ i ∈ range 0, 1 = 0`. Since `range 0 = ∅`
    and the sum over `∅` is `0`, both sides reduce to `0`."
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "You have `ih : ∑ i ∈ range n, 1 = n`.
    The goal is `∑ i ∈ range (n + 1), 1 = n + 1`.

    First, peel off the last term with `rw [Finset.sum_range_succ]`.
    Then apply the inductive hypothesis with `rw [ih]`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]`."
    rw [Finset.sum_range_succ, ih]

Conclusion
"
Congratulations on your first inductive sum proof!

## The three-step pattern

Every inductive proof on range sums follows this template:

1. **`induction n with`** — split into base case and inductive step.
2. **Base case**: `rfl` (or `rw [range_zero, sum_empty]`), since the
   sum over an empty range is `0`.
3. **Inductive step**: `rw [sum_range_succ, ih]`, then close the
   arithmetic.

In this level the arithmetic was trivial (both sides became `n + 1`
after rewriting). In harder levels, you will need `ring` or `omega` to
close the final equality.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
