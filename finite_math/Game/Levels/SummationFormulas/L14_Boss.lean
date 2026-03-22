import Game.Metadata

World "SummationFormulas"
Level 14

Title "Boss: The Factorial Sum Identity"

Introduction "
# Boss: The Factorial Sum Identity

Prove this striking identity connecting sums and factorials:

$$\\left(\\sum_{i=0}^{n-1} i \\cdot i!\\right) + 1 = n!$$

The key insight: each term $i \\cdot i!$ equals $(i+1)! - i!$
(since $(i+1)! = (i+1) \\cdot i! = i \\cdot i! + i!$). So the sum
telescopes: all intermediate factorials cancel, leaving $n! - 0! = n! - 1$.

This is a **telescoping sum** — each term equals a difference of
consecutive factorials, so the intermediate terms cancel. In Level 12,
you saw telescoping with squares; here the function is the factorial.

Your proof uses induction with the range-peel + IH pattern, but the
inductive step involves factorial terms — so `ring` alone won't close it.
You'll need the **have + ring + omega** technique from Levels 5-7.

**What you need** (all from this world):
- Natural number induction
- `Finset.sum_range_zero` and `Finset.sum_range_succ`
- `Nat.factorial_succ`
- `have ... := by ring` to establish a factorial identity
- `omega` to close the final linear arithmetic
"

/-- The sum of i * i! for i in range n, plus 1, equals n factorial. -/
Statement (n : ℕ) : (∑ i ∈ Finset.range n, i * Nat.factorial i) + 1 = Nat.factorial n := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The sum over `range 0` is empty, so the
    left side is $0 + 1 = 1$. The right side is $0! = 1$."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero, Nat.factorial_zero]`."
    rw [Finset.sum_range_zero, Nat.factorial_zero]
  | succ n ih =>
    Hint "**Inductive step**: Peel the last term $n \\cdot n!$ with
    `sum_range_succ`, then unfold $(n+1)!$ with `factorial_succ`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Nat.factorial_succ]`."
    rw [Finset.sum_range_succ, Nat.factorial_succ]
    Hint "The goal now involves `(n+1) * Nat.factorial n` on the right.
    You need to connect this to the left side, which has
    `n * Nat.factorial n` and the IH.

    Use `have` to establish that $(n+1) \\cdot n! = n! + n \\cdot n!$
    (which `ring` can prove), then `rw` it into the goal."
    Hint (hidden := true) "Try:
    `have h : (n + 1) * Nat.factorial n = Nat.factorial n + n * Nat.factorial n := by ring`
    then `rw [h]`."
    have h : (n + 1) * Nat.factorial n = Nat.factorial n + n * Nat.factorial n := by ring
    Hint "After `rw [h]`, the goal becomes linear in the opaque quantities
    `sum`, `Nat.factorial n`, and `n * Nat.factorial n`.
    The IH gives `sum + 1 = Nat.factorial n`, so `omega` can close it."
    Hint (hidden := true) "Try `rw [h]` then `omega`."
    rw [h]
    omega

Conclusion "
Congratulations! You proved the factorial sum identity:
$$\\left(\\sum_{i=0}^{n-1} i \\cdot i!\\right) + 1 = n!$$

**Telescoping sums**: This is your second telescoping sum (after
Level 12's squares). Since $i \\cdot i! = (i+1)! - i!$, the sum
collapses:
$$\\sum_{i=0}^{n-1} [(i+1)! - i!] = n! - 0! = n! - 1$$

All intermediate terms cancel in pairs. You've now seen telescoping
with two different functions — $f(i) = i^2$ and $f(i) = i!$ — so the
pattern should feel transferable: whenever each term is a difference
of consecutive values of some function, the sum telescopes.

**Skills integrated in this boss**:
1. `induction n with` — natural number induction (Level 1)
2. `Finset.sum_range_zero` — base case (Level 1)
3. `Finset.sum_range_succ` — range-peel (Level 1)
4. `Nat.factorial_succ` — factorial unfolding (Level 10)
5. `have ... := by ring` — establishing a non-polynomial identity (Levels 5-7)
6. `rw [h]` — rewriting with a local hypothesis
7. `omega` — closing linear arithmetic (Levels 5-7)

**Note on `mul_add`**: In Levels 2, 4, and 6, you used `mul_add`
to distribute a constant factor before substituting the IH. The
`have h := ... by ring` technique generalizes this — `ring` can
prove `a * (b + c) = a * b + a * c` and any other ring identity,
so `have` + `ring` subsumes `mul_add` as a special case.

**The unified method**: natural number induction + range-peeling +
algebraic closure. Whether the closure is `ring` alone,
`mul_add` + `ring`, or `have` + `ring` + `omega` depends on the
formula's structure, but the inductive skeleton is always the same.
"

/-- Disabled: directly gives `n! = ∏ i ∈ range n, (i + 1)`. -/
TheoremDoc Nat.factorial_eq_prod_range_add_one as "Nat.factorial_eq_prod_range_add_one" in "Nat"
/-- Disabled: directly gives `∏ i ∈ range n, (i + 1) = n!`. -/
TheoremDoc Finset.prod_range_add_one_eq_factorial as "Finset.prod_range_add_one_eq_factorial" in "BigOp"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub Nat.factorial_eq_prod_range_add_one Finset.prod_range_add_one_eq_factorial Finset.sum_range_id_mul_two Finset.sum_range_id
