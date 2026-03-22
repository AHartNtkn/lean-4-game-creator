import Game.Metadata

World "PascalsTriangle"
Level 6

Title "The Reindexing Correspondence"

Introduction "
# Why Reindexing Works

In the next level, you will use a reindexing lemma that converts
a sum over `antidiagonal n` into a sum over `range (n + 1)`. The
correspondence maps each index $k$ to the pair $(k, n - k)$.

But why does this work? Because $(k, n - k)$ is **always** in
`antidiagonal n` when $k \\le n$: the coordinates sum to
$k + (n - k) = n$.

**Your task**: Prove that $(k, n - k) \\in \\text{antidiagonal}(n)$
given $k \\le n$.

This is the membership fact that makes the reindexing valid.
Every pair in the antidiagonal has the form $(k, n - k)$ for
some $k \\le n$, and conversely every such pair is in the
antidiagonal. You are proving the converse direction.
"

/-- (k, n - k) is in the antidiagonal of n when k ≤ n. -/
Statement (n k : ℕ) (hk : k ≤ n) : (k, n - k) ∈ Finset.antidiagonal n := by
  Hint "Convert the membership condition to arithmetic using
  `Finset.mem_antidiagonal`. Then the goal becomes
  `k + (n - k) = n`, which follows from `k ≤ n`."
  Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal]`."
  rw [Finset.mem_antidiagonal]
  Hint "The goal is `k + (n - k) = n`. Since `k ≤ n`, this is
  a standard arithmetic fact. Use `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
$(k, n - k) \\in \\text{antidiagonal}(n)$ because $k + (n - k) = n$.

This is the **reindexing correspondence**: for each $k$ with
$0 \\le k \\le n$, the pair $(k, n - k)$ is in the antidiagonal.
Conversely, every pair $(i, j)$ in the antidiagonal satisfies
$j = n - i$ (since $i + j = n$). So the antidiagonal is exactly
$\\{(0, n), (1, n-1), \\ldots, (n, 0)\\}$, which has $n + 1$
elements (matching `card_antidiagonal` from Level 5).

This bijection between $\\{0, 1, \\ldots, n\\}$ and
`antidiagonal n` is what makes the reindexing lemma
`sum_antidiagonal_eq_sum_range_succ_mk` true: it converts
a sum over pairs $(i, j)$ with $i + j = n$ into a sum over
a single index $k \\in \\{0, \\ldots, n\\}$, replacing each pair
with $(k, n - k)$.

In the next level, you will use this reindexing to compute
a row sum of Pascal's triangle through the antidiagonal.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
