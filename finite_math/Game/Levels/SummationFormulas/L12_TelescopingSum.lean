import Game.Metadata

World "SummationFormulas"
Level 12

Title "A Telescoping Sum"

Introduction "
# Telescoping Sums

In Level 3, you proved $\\sum_{i=0}^{n-1} (2i + 1) = n^2$ using
the standard range-peel + IH + ring pattern. Here's the same result
stated differently:

$$\\sum_{i=0}^{n-1} \\left((i+1)^2 - i^2\\right) = n^2$$

Why is this the same? Because $(i+1)^2 - i^2 = i^2 + 2i + 1 - i^2 = 2i + 1$.
Each term is the **difference between consecutive squares**. When you
write out the sum, all intermediate squares cancel:

$$(1^2 - 0^2) + (2^2 - 1^2) + (3^2 - 2^2) + \\cdots + (n^2 - (n-1)^2)
= n^2 - 0^2 = n^2$$

This is a **telescoping sum**: each term is a difference $f(i+1) - f(i)$
for some function $f$, so all intermediate values cancel and only the
endpoints survive: $f(n) - f(0)$.

**Your task**: Prove this by induction. The base case is straightforward.
In the inductive step, after peeling and substituting the IH, use
`have + ring + omega`: `ring` proves $(n+1)^2 = n^2 + (2n+1)$, and
`omega` handles the resulting natural number arithmetic.
"

/-- The sum of (i+1)² - i² over range n equals n². A telescoping sum. -/
Statement (n : ℕ) : ∑ i ∈ Finset.range n, ((i + 1) ^ 2 - i ^ 2) = n ^ 2 := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The sum over `range 0` is empty, so $0 = 0^2 = 0$."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel the last term with `sum_range_succ`
    and substitute the IH."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]`."
    rw [Finset.sum_range_succ, ih]
    Hint "The goal is `n ^ 2 + ((n + 1) ^ 2 - n ^ 2) = (n + 1) ^ 2`.

    This involves natural number subtraction, so `ring` can't close it
    directly. Use `have + ring + omega`: establish $(n+1)^2 = n^2 + (2n+1)$
    with `ring`, then `omega` handles the subtraction arithmetic."
    Hint (hidden := true) "Try:
    `have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring`
    then `omega`."
    have h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1) := by ring
    Hint "Now `omega` sees:
    - `h : (n + 1) ^ 2 = n ^ 2 + (2 * n + 1)`
    - Goal: `n ^ 2 + ((n + 1) ^ 2 - n ^ 2) = (n + 1) ^ 2`

    Substituting `h`, this becomes `n^2 + (2n+1) = n^2 + (2n+1)` — trivially true."
    Hint (hidden := true) "Try `omega`."
    omega

Conclusion "
You proved that $\\sum_{i=0}^{n-1} ((i+1)^2 - i^2) = n^2$.

**What makes it telescoping?** Each term $(i+1)^2 - i^2$ is the
difference between consecutive values of the function $f(i) = i^2$.
When you add up these differences, all intermediate values cancel —
only the endpoints survive: $f(n) - f(0) = n^2 - 0 = n^2$.

**Connection to Level 3**: You already proved
$\\sum (2i + 1) = n^2$ using range-peel + IH + ring. That identity
and this one are the same sum in different notation, since
$(i+1)^2 - i^2 = 2i + 1$. But the telescoping viewpoint is more
powerful: it tells you *why* the sum has a closed form, not just
*that* it does.

In the boss (Level 14), you'll see another telescoping sum where
$f(i) = i!$. Each term $i \\cdot i! = (i+1)! - i!$, so the sum
collapses to $n! - 0! = n! - 1$. Whenever each term is a difference
of consecutive values of some function, you're looking at a
telescoping sum.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Nat.factorial_eq_prod_range_add_one Finset.prod_range_add_one_eq_factorial Finset.sum_range_id_mul_two Finset.sum_range_id
