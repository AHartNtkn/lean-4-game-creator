import Game.Metadata

World "PascalsTriangle"
Level 7

Title "Row Sum via Antidiagonal"

Introduction "
# Row Sum Through Pairs

In BinomialTheorem Level 8, you proved:
$$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$$

Now express the same sum **through the antidiagonal**. For each
pair $(i, j)$ with $i + j = n$, take the entry $\\binom{n}{i}$
(indexed by the first coordinate). The sum of all such entries
is the row sum.

**Proof plan**:
1. Reindex: convert the antidiagonal sum to a range sum using
   `sum_antidiagonal_eq_sum_range_succ_mk`
2. Close: apply `Nat.sum_range_choose` (the row sum identity)

The **reindexing lemma** converts between the two:

```
Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk (g : ℕ × ℕ → M) (n : ℕ) :
  ∑ p ∈ Finset.antidiagonal n, g p =
    ∑ k ∈ Finset.range (n + 1), g (k, n - k)
```

Since every pair $(i, j)$ in the antidiagonal satisfies $j = n - i$,
you can replace the pair-sum with a single-index sum where $k$ ranges
from $0$ to $n$ and the second argument is $n - k$.
"

/-- `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` states that
`∑ p ∈ antidiagonal n, g p = ∑ k ∈ range (n + 1), g (k, n - k)`.

## Syntax
```
rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
```

## When to use it
When you have a sum over `antidiagonal n` with a function
`g : ℕ × ℕ → M` applied to the pair `p` directly (not split
into `p.1` and `p.2`). This variant handles functions like
`fun p => choose n p.1` where the second coordinate is not used.

## Difference from `sum_antidiagonal_eq_sum_range_succ`
The non-`_mk` version requires the summand to have the form
`f p.1 p.2` (curried). This `_mk` version handles `g p` (uncurried).
-/
TheoremDoc Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk as "Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk" in "Finset"

/-- The row sum via antidiagonal: ∑ (i,j) with i+j=n of C(n,i) = 2^n. -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.1 = 2 ^ n := by
  Hint "The summand is `choose n p.1` — a function of the pair `p`
  that only uses the first coordinate. Reindex to a range sum using
  the `_mk` variant of the reindexing lemma."
  Hint (hidden := true) "Try `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`."
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  Hint "After reindexing, the goal is:
  `∑ k ∈ range (n + 1), Nat.choose n (k, n - k).1 = 2 ^ n`

  Since `(k, n - k).1 = k`, this simplifies to
  `∑ k ∈ range (n + 1), Nat.choose n k = 2 ^ n`.

  This is exactly `Nat.sum_range_choose` from BinomialTheorem."
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion "
Two steps: reindex, then apply the row sum.

$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i}
\\;\\xrightarrow{\\text{reindex}}\\;
\\sum_{k=0}^{n} \\binom{n}{k}
\\;\\xrightarrow{\\text{sum\\_range\\_choose}}\\;
2^n$$

**The point**: The antidiagonal is a different **lens** on the same
sum. In the `range` view, you sum over one index $k$.
In the `antidiagonal` view, you sum over pairs $(i, j)$ with
$i + j = n$. The reindexing lemma lets you move freely between
the two views. The mathematics is the same; only the bookkeeping
changes.

In the next level, you will see why the antidiagonal view matters:
it makes **symmetry** visible.
"

NewTheorem Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
