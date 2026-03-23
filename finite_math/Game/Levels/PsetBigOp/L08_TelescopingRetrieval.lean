import Game.Metadata

World "PsetBigOp"
Level 8

Title "Telescoping: Consecutive Products"

Introduction "
# Telescoping Retrieval

In SummationFormulas, you proved a **telescoping sum** where each
term was a difference of consecutive squares: $(i+1)^2 - i^2$.
Here is a fresh instance of the same technique with a different
function.

Prove:

$$\\sum_{i=0}^{n-1} \\bigl((i+1)(i+2) - i(i+1)\\bigr) = n(n+1)$$

**Why does it telescope?** Each term is $f(i+1) - f(i)$ where
$f(i) = i(i+1)$. When you write out the sum:

$$(1 \\cdot 2 - 0 \\cdot 1) + (2 \\cdot 3 - 1 \\cdot 2) + \\cdots + (n(n+1) - (n-1)n) = n(n+1) - 0 = n(n+1)$$

All intermediate products cancel — only the endpoints survive.

**Your task**: Prove this by induction on `n`, using the same
range-peel + IH + `have`/`ring`/`omega` technique as before.
"

/-- The sum of (i+1)*(i+2) - i*(i+1) over range n equals n*(n+1). A telescoping sum. -/
Statement (n : ℕ) : ∑ i ∈ Finset.range n, ((i + 1) * (i + 2) - i * (i + 1)) = n * (n + 1) := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The sum over `range 0` is empty."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel the last term with `sum_range_succ`
    and substitute the IH."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]`."
    rw [Finset.sum_range_succ, ih]
    Hint "The goal involves natural number subtraction:
    `n * (n + 1) + ((n + 1) * (n + 2) - n * (n + 1)) = (n + 1) * (n + 2)`.

    Use the `have` + `ring` + `rw` + `omega` technique: establish that
    $(n+1)(n+2) = n(n+1) + 2(n+1)$ with `ring`, rewrite with `rw [h]`
    to eliminate the product $(n+1)(n+2)$, then `omega` handles the
    resulting subtraction arithmetic."
    Hint (hidden := true) "Try:
    `have h : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring`
    then `rw [h]` then `omega`."
    have h : (n + 1) * (n + 2) = n * (n + 1) + 2 * (n + 1) := by ring
    Hint "Now rewrite with `h` to replace $(n+1)(n+2)$ everywhere:

    `rw [h]`

    After rewriting, the only nonlinear term is $n(n+1)$, and
    the subtraction $n(n+1) + 2(n+1) - n(n+1)$ simplifies to
    $2(n+1)$. Then `omega` closes the linear arithmetic."
    Hint (hidden := true) "Try `rw [h]` then `omega`."
    rw [h]
    omega

Conclusion "
You proved that $\\sum_{i=0}^{n-1} ((i+1)(i+2) - i(i+1)) = n(n+1)$.

**Telescoping with consecutive products**: Each term
$(i+1)(i+2) - i(i+1)$ is the difference between consecutive values
of $f(i) = i(i+1)$. All intermediate values cancel, leaving
$f(n) - f(0) = n(n+1) - 0 = n(n+1)$.

**Arithmetic check**: $(i+1)(i+2) - i(i+1) = (i+1)(i+2-i) = 2(i+1)$.
So this is also $\\sum 2(i+1) = 2(1 + 2 + \\cdots + n) = n(n+1)$ — the
familiar sum-of-first-n formula. The telescoping viewpoint and the
direct computation give the same answer, as they must.

**The technique transfers**: In SummationFormulas you telescoped
with $f(i) = i^2$ (squares) and $f(i) = i!$ (factorial). Here,
$f(i) = i(i+1)$ (consecutive products). The proof skeleton is
identical every time: induction, range-peel, IH, then `have` +
`ring` + `rw` + `omega` to close the gap. (In simpler cases like
squares, the `rw` step is optional — `omega` can handle it directly.
With products of distinct factors, the extra `rw` helps `omega`
by reducing the number of nonlinear terms.)
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id
