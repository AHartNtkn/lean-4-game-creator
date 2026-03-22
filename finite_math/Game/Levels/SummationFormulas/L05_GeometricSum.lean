import Game.Metadata

World "SummationFormulas"
Level 5

Title "Geometric Sum"

Introduction "
# The Geometric Series Formula

The **geometric sum** states:

$$\\sum_{i=0}^{n-1} 2^i = 2^n - 1$$

Since natural number subtraction is floor subtraction ($2^n - 1$
could misbehave when $n = 0$ if we weren't careful), we state this
as:

$$\\left(\\sum_{i=0}^{n-1} 2^i\\right) + 1 = 2^n$$

The proof follows the same range-peel + IH pattern, but the closing
step is different. After peeling and using the IH, you'll need to
show $2^n + 2^n = 2^{n+1}$. This isn't a polynomial identity
(it involves exponentials), so `ring` alone won't close it.

**Strategy**: Use `have` to establish $2^{n+1} = 2 \\cdot 2^n$ (which
`ring` *can* prove), then `omega` closes the resulting linear goal.
"

/-- The geometric sum: the sum of powers of 2 plus 1 equals 2 to the n. -/
Statement (n : ℕ) : (∑ i ∈ Finset.range n, 2 ^ i) + 1 = 2 ^ n := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: `range 0` is empty, so the sum is $0$.
    The goal becomes $0 + 1 = 2^0 = 1$."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel off $2^n$ with `sum_range_succ`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ]`."
    rw [Finset.sum_range_succ]
    Hint "The goal is now
    `(∑ i ∈ range n, 2^i + 2^n) + 1 = 2^(n+1)`.

    If you tried `ring` here, it won't work — `ring` treats `2^n`
    and `2^(n+1)` as related ring expressions but can't use the
    induction hypothesis. And `rw [ih]` won't fire because the IH's
    pattern `(∑ ...) + 1` doesn't appear literally in the goal.

    **New strategy**: Use `have` to tell Lean that `2^(n+1) = 2 * 2^n`
    (which `ring` *can* prove), then `omega` handles the rest as
    linear arithmetic."
    Hint (hidden := true) "Try:
    `have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring`
    then `omega`."
    have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    Hint "Now `omega` sees:
    - `ih : ∑ + 1 = 2^n`
    - `h : 2^(n+1) = 2 * 2^n`
    - Goal: `(∑ + 2^n) + 1 = 2^(n+1)`

    Treating `∑`, `2^n`, and `2^(n+1)` as opaque naturals, this is
    linear arithmetic: $(\\Sigma + a) + 1 = b$ given $\\Sigma + 1 = a$
    and $b = 2a$."
    Hint (hidden := true) "Try `omega`."
    omega

Conclusion "
You proved the geometric sum formula:
$$\\sum_{i=0}^{n-1} 2^i + 1 = 2^n$$

**New technique**: When the goal involves exponentials, `ring` can
prove identities like $2^{n+1} = 2 \\cdot 2^n$, but `omega`
handles the final linear rearrangement. The combination
`have h := ... by ring; omega` is a useful strategy when neither
tactic alone suffices.

**Why omega works here**: After `have h`, the goal and hypotheses
form a *linear* system in the opaque quantities $\\Sigma$, $2^n$,
and $2^{n+1}$. `omega` solves linear arithmetic over naturals,
treating these as unknown non-negative integers.

**Division of labor**: `ring` proves polynomial identities involving
variables (like $2^{n+1} = 2 \\cdot 2^n$) but cannot handle
inequalities or do case analysis. `omega` handles linear arithmetic
(equalities and inequalities) but cannot reason about nonlinear
expressions like $2^n$. The `have + ring + omega` combination works
because `ring` reduces the nonlinear parts to named hypotheses, and
`omega` handles the resulting linear problem.

The formula generalizes: for any base $q \\ne 1$,
$$\\sum_{i=0}^{n-1} q^i = \\frac{q^n - 1}{q - 1}$$
We proved the $q = 2$ case, where the denominator is just $1$.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.geom_sum_eq Finset.geom_series_def Finset.pow_eq_prod_const Finset.prod_const
