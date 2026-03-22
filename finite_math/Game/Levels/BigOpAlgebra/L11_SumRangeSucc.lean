import Game.Metadata

World "BigOpAlgebra"
Level 11

Title "Peeling Off the Last Term"

Introduction "
# sum_range_succ: The Split-Off-the-Last-Term Lemma

When summing over `Finset.range (n + 1) = {0, 1, ..., n}`, you
can peel off the **last** term:

$$\\sum_{i=0}^{n} f(i) = \\Bigl(\\sum_{i=0}^{n-1} f(i)\\Bigr) + f(n)$$

In Lean:
```
Finset.sum_range_succ (f : ℕ → M) (n : ℕ) :
  ∑ i ∈ Finset.range (n + 1), f i =
    (∑ i ∈ Finset.range n, f i) + f n
```

Compare this to `sum_insert` from BigOpIntro, which peels off
the **first** element of `insert a s`. `sum_range_succ` peels off
the **last** element of a range. Both decompose a sum by removing
one term.

**Why this matters**: `sum_range_succ` is the engine that drives
inductive proofs about summation formulas. To prove something about
`∑ i ∈ range (n+1), f i`, you split off `f n` and apply the
induction hypothesis to `∑ i ∈ range n, f i`. You'll see this
pattern extensively in later worlds.

**Your task**: Given the sum over `range n`, compute the sum over
`range (n + 1)`.
"

/-- Peel off the last term of a range sum. -/
Statement (f : ℕ → ℕ) (n : ℕ) (h : ∑ i ∈ Finset.range n, f i = 100) :
    ∑ i ∈ Finset.range (n + 1), f i = 100 + f n := by
  Hint "Use `rw [Finset.sum_range_succ]` to peel off the last term
  `f n` from the sum over `range (n + 1)`."
  rw [Finset.sum_range_succ]
  Hint "The goal is now `(∑ i ∈ range n, f i) + f n = 100 + f n`.
  Substitute the known sum with `rw [h]`."
  Hint (hidden := true) "Try `rw [h]`."
  rw [h]

Conclusion "
`sum_range_succ` peels one term off the top of a range sum:

$$\\sum_{i \\in \\text{range}(n+1)} f(i) = \\sum_{i \\in \\text{range}(n)} f(i) + f(n)$$

Combined with induction on `n`, this gives a complete strategy for
proving summation formulas:
- **Base case**: `∑ i ∈ range 0, f i = 0` (by `sum_empty`, since `range 0 = ∅`)
- **Inductive step**: `sum_range_succ` peels off `f n`, then the IH
  handles the remaining sum

You'll use this pattern heavily in the FinsetInduction and
SummationFormulas worlds.
"

/-- `Finset.sum_range_succ` states that
`∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n`.

Peels off the last term of a sum over `Finset.range`.

## Syntax
```
rw [Finset.sum_range_succ]
exact Finset.sum_range_succ f n
```

## When to use it
When you see `∑ i ∈ Finset.range (n + 1), f i` and want to
separate the last term `f n` from the rest.

## Example
```
-- Goal: ∑ i ∈ range (n + 1), f i = (∑ i ∈ range n, f i) + f n
rw [Finset.sum_range_succ]
```

## Connection
This is the range-based analogue of `sum_insert` (which peels from
the front of `insert a s`). Both decompose a sum by removing one
term — `sum_insert` removes the first, `sum_range_succ` removes
the last.
-/
TheoremDoc Finset.sum_range_succ as "Finset.sum_range_succ" in "BigOp"

NewTheorem Finset.sum_range_succ Finset.sum_range_succ'

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
