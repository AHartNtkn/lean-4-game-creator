import Game.Metadata

World "SummationFormulas"
Level 6

Title "Geometric Sum: Base 3"

Introduction "
# The Geometric Sum for $q = 3$

In the previous level, you proved the geometric sum for base $2$:
$\\sum_{i=0}^{n-1} 2^i + 1 = 2^n$. That formula worked out cleanly
because the denominator in the general formula $\\frac{q^n - 1}{q - 1}$
is just $1$ when $q = 2$.

For $q = 3$, the denominator is $2$:
$$\\sum_{i=0}^{n-1} 3^i = \\frac{3^n - 1}{2}$$

To avoid division, multiply both sides by $2$:
$$2 \\cdot \\sum_{i=0}^{n-1} 3^i + 1 = 3^n$$

**The proof** uses the same **have + ring + omega** technique from Level 5.
After peeling with `sum_range_succ`, you distribute the $2$ with `mul_add`
(just like the Gauss sum), establish $3^{n+1} = 3 \\cdot 3^n$ with `have`,
and close with `omega`.

This is your second exposure to **have + ring + omega** — you'll need it
again in the boss.
"

/-- Twice the sum of powers of 3, plus 1, equals 3 to the n. -/
Statement (n : ℕ) : 2 * (∑ i ∈ Finset.range n, 3 ^ i) + 1 = 3 ^ n := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: `range 0` is empty, so the sum is $0$.
    The goal becomes $2 \\cdot 0 + 1 = 3^0 = 1$."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel with `sum_range_succ`, then
    distribute the $2$ with `mul_add` — this separates the sum
    (which the IH knows about) from the new $3^n$ term."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, mul_add]`."
    rw [Finset.sum_range_succ, mul_add]
    Hint "Now you need to connect `3^(n+1)` to `3 * 3^n`.
    Use `have` to establish this identity (which `ring` can prove),
    then `omega` closes the linear arithmetic using the IH."
    Hint (hidden := true) "Try:
    `have h : 3 ^ (n + 1) = 3 * 3 ^ n := by ring`
    then `omega`."
    have h : 3 ^ (n + 1) = 3 * 3 ^ n := by ring
    Hint "Now `omega` sees:
    - `ih : 2 * ∑ + 1 = 3^n`
    - `h : 3^(n+1) = 3 * 3^n`
    - Goal: `2 * ∑ + 2 * 3^n + 1 = 3^(n+1)`

    This is linear in the opaque quantities."
    Hint (hidden := true) "Try `omega`."
    omega

Conclusion "
You proved the geometric sum formula for base $3$:
$$2\\sum_{i=0}^{n-1} 3^i + 1 = 3^n$$

**Pattern comparison with Level 5** ($q = 2$):

| Step | $q = 2$ | $q = 3$ |
|------|---------|---------|
| Multiply-both-sides factor | $1$ (trivial) | $2$ |
| Peel | `sum_range_succ` | `sum_range_succ` + `mul_add` |
| Close | `have (2^{n+1} = 2 \\cdot 2^n)` + `omega` | `have (3^{n+1} = 3 \\cdot 3^n)` + `omega` |

The $q = 3$ case forced you to use `mul_add` to distribute the constant
factor — the same move you used in the Gauss sum (Level 2) and sum of
squares (Level 4). The **have + ring + omega** technique is unchanged:
`ring` proves the exponential identity, `omega` handles the linear
rearrangement.

**General pattern**: for any base $q \\ne 1$,
$(q - 1) \\cdot \\sum_{i=0}^{n-1} q^i + 1 = q^n$.
The proof is structurally the same for every $q$. In the next
level, you will prove this general formula — and see that the
proof requires zero structural changes from the specific cases.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.geom_sum_eq Finset.geom_series_def Finset.pow_eq_prod_const Finset.prod_const
