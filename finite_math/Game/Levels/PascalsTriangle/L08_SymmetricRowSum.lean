import Game.Metadata

World "PascalsTriangle"
Level 8

Title "The Symmetric Row Sum"

Introduction "
# Summing the Second Coordinate

In Level 7, you proved:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{i} = 2^n$$

Now prove the **symmetric version**: index by the **second** coordinate
instead:
$$\\sum_{(i,j) \\in \\text{antidiagonal}(n)} \\binom{n}{j} = 2^n$$

This should give the same answer — after all, summing a row of
Pascal's triangle from left to right or from right to left
produces the same total. But the formal proof requires a new tool.

The **swap lemma**:
```
Finset.Nat.sum_antidiagonal_swap :
  ∑ p ∈ Finset.antidiagonal n, f p.swap =
    ∑ p ∈ Finset.antidiagonal n, f p
```

This says: swapping the coordinates of each pair does not change
the sum. Since swapping replaces $(i, j)$ with $(j, i)$, and the
antidiagonal is symmetric in $i$ and $j$, the sum is unchanged.

**Proof plan**:
1. Use `← Finset.Nat.sum_antidiagonal_swap` (backward!) to rewrite
   the sum: since `p.swap.2 = p.1`, the backward rewrite converts
   `∑ choose n p.2` into `∑ choose n p.swap.2 = ∑ choose n p.1`
2. Reindex to a range sum
3. Apply `Nat.sum_range_choose`
"

/-- `Finset.Nat.sum_antidiagonal_swap` states that
`∑ p ∈ antidiagonal n, f p.swap = ∑ p ∈ antidiagonal n, f p`.

## Syntax
```
rw [Finset.Nat.sum_antidiagonal_swap]
rw [← Finset.Nat.sum_antidiagonal_swap]
```

## When to use it
When you want to swap the roles of `p.1` and `p.2` in a sum
over the antidiagonal. The forward direction replaces `f p.swap`
with `f p`. The backward direction (`←`) replaces `f p` with
`f p.swap`, which effectively swaps `p.1 ↔ p.2` throughout the
summand.

## Warning
The backward direction (`←`) is usually what you want when you
need to convert a sum over `p.2` into a sum over `p.1`.
-/
TheoremDoc Finset.Nat.sum_antidiagonal_swap as "Finset.Nat.sum_antidiagonal_swap" in "Finset"

/-- The symmetric row sum: ∑ (i,j) with i+j=n of C(n,j) = 2^n. -/
Statement (n : ℕ) :
    ∑ p ∈ Finset.antidiagonal n, Nat.choose n p.2 = 2 ^ n := by
  Hint "The summand uses `p.2` instead of `p.1`. You need to swap
  the coordinates. Use `← Finset.Nat.sum_antidiagonal_swap` to
  convert the sum: after swapping, `p.swap.2 = p.1`."
  Hint (hidden := true) "Try `rw [← Finset.Nat.sum_antidiagonal_swap]`.

  The `←` (backward) direction converts
  `∑ p, f p` into `∑ p, f p.swap`.
  Here `f p = choose n p.2`, so `f p.swap = choose n p.swap.2 = choose n p.1`."
  rw [← Finset.Nat.sum_antidiagonal_swap]
  Hint "Good — the sum now uses `p.1` instead of `p.2`.
  Reindex and apply the row sum identity."
  Hint (hidden := true) "Try `rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]`."
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  Hint "The goal is the row sum identity. Close with `sum_range_choose`."
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion "
Three steps: swap, reindex, close.

$$\\sum_{(i,j)} \\binom{n}{j}
\\;\\xrightarrow{\\text{swap}}\\;
\\sum_{(i,j)} \\binom{n}{i}
\\;\\xrightarrow{\\text{reindex}}\\;
\\sum_{k=0}^{n} \\binom{n}{k}
= 2^n$$

**Why the swap works**: Coordinate-swapping $(i, j) \\mapsto (j, i)$
is a **bijection** on the antidiagonal because $i + j = n$ if and
only if $j + i = n$. Since it is a bijection, it only permutes
the terms of the sum — it cannot add or remove any — so the
total is unchanged. This is the formal version of the intuition
that the antidiagonal \"looks the same\" under reflection.

This is a **change of variable** argument. In ordinary math, you
would write: \"Let $k = j$ and $n - k = i$; then the sum becomes
$\\sum_k \\binom{n}{k} = 2^n$.\" The formal version is more explicit:
swap the pair coordinates, then reindex.

**The swap-reindex pattern**: You now have a three-step strategy
for any antidiagonal sum involving the second coordinate:
1. **Swap** — use `← sum_antidiagonal_swap` to turn `p.2` into `p.1`
2. **Reindex** — use `sum_antidiagonal_eq_sum_range_succ_mk` to convert
   to a single-index sum over `range`
3. **Close** — apply a known range-sum identity

This swap-reindex pattern is a reusable proof strategy — an
**antidiagonal change of variable**. You will see it again in
the boss level.
"

NewTheorem Finset.Nat.sum_antidiagonal_swap

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
