import Game.Metadata

World "SummationFormulas"
Level 8

Title "An Exponential Bound"

Introduction "
# Inequality by Induction

Every level so far in this world proved an **equality** by induction.
Now you'll prove an **inequality**: exponential growth always outpaces
linear growth.

$$n + 1 \\le 2^n$$

The proof uses the same `have + ring + omega` technique from Levels
5-7, but with a crucial difference: `omega` closes an **inequality**
rather than an equality. In the inductive step, you need to show that
$n + 2 \\le 2^{n+1}$, given $n + 1 \\le 2^n$. The key identity
$2^{n+1} = 2 \\cdot 2^n$ (proved by `ring`) turns this into linear
arithmetic that `omega` can handle.

**Why this matters**: Many counting arguments need bounds, not just
exact formulas. The `have + ring + omega` pattern works for both.
When `omega` closes the final step, it doesn't care whether the goal
is `=` or `\\le` — it handles any linear relation over naturals.
"

/-- Exponential growth outpaces linear growth: n + 1 is at most 2 to the n. -/
Statement (n : ℕ) : n + 1 ≤ 2 ^ n := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The goal is $0 + 1 \\le 2^0$, i.e., $1 \\le 1$.
    Use `have + ring + omega` to handle the exponential."
    Hint (hidden := true) "Try:
    `have h : 2 ^ (0 : ℕ) = 1 := by ring`
    then `omega`."
    have h : 2 ^ (0 : ℕ) = 1 := by ring
    omega
  | succ n ih =>
    Hint "**Inductive step**: You have `ih : n + 1 \\le 2^n` and need
    to show `n + 2 \\le 2^(n+1)`.

    Use `have` to establish $2^(n+1) = 2 \\cdot 2^n$ (which `ring`
    can prove). Then `omega` sees:
    - `ih : n + 1 \\le 2^n` (i.e., $a \\ge n+1$)
    - `h : 2^(n+1) = 2 \\cdot 2^n$ (i.e., $b = 2a$)
    - Goal: $n+2 \\le b$

    Since $b = 2a \\ge 2(n+1) = 2n+2 \\ge n+2$, this is linear arithmetic."
    Hint (hidden := true) "Try:
    `have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring`
    then `omega`."
    have h : 2 ^ (n + 1) = 2 * 2 ^ n := by ring
    Hint "Now `omega` has all the linear facts it needs."
    Hint (hidden := true) "Try `omega`."
    omega

Conclusion "
You proved that $n + 1 \\le 2^n$ for all natural numbers.

**Equality vs. inequality induction**: The proof structure is
identical to the equality proofs in Levels 5-7 — induct, establish
an algebraic identity with `have + ring`, close with `omega`. The
only difference is that `omega` proved $\\le$ instead of $=$. The
`omega` tactic handles any linear arithmetic over naturals, whether
the goal is an equation or an inequality.

**The inductive step in detail**: From `ih : n + 1 \\le 2^n` and
`h : 2^(n+1) = 2 * 2^n`, `omega` chains:
$$n + 2 \\le 2(n+1) \\le 2 \\cdot 2^n = 2^{n+1}$$
The first inequality uses $n \\ge 0$; the second multiplies the IH
by 2. This is a **monotonicity argument** — the inductive step works
because multiplication by a positive constant preserves inequalities.

**Division of labor**: `ring` handles polynomial identities (like
$2^{n+1} = 2 \\cdot 2^n$), while `omega` handles linear arithmetic
(both equalities and inequalities). `ring` cannot prove inequalities;
`omega` cannot handle nonlinear expressions. Together, they cover
most inductive steps you'll encounter.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.geom_sum_eq Finset.geom_series_def Finset.pow_eq_prod_const Finset.prod_const Nat.lt_two_pow Nat.lt_pow_self
