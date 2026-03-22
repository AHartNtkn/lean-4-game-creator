import Game.Metadata

World "SummationFormulas"
Level 1

Title "Summing 1s Over a Range"

Introduction "
# Natural Number Induction for Sums

In the FinsetInduction world, you proved sum identities by induction on
an *arbitrary finset* $s$ using `Finset.induction_on`. The base case was
$s = \\emptyset$ and the step was $s \\to \\text{insert}\\ a\\ s$.

In this world, you'll prove **classical summation formulas** — identities
about $\\sum_{i=0}^{n-1} f(i)$ — using a different pattern: **natural
number induction** combined with `sum_range_succ`.

The idea: sums over `Finset.range n` are naturally indexed by $n$, so
you induct on $n$ directly:

- **Base case** ($n = 0$): `Finset.sum_range_zero` gives
  $\\sum_{i \\in \\text{range } 0} f(i) = 0$

- **Inductive step** ($n \\to n+1$): `Finset.sum_range_succ` gives
  $\\sum_{i \\in \\text{range}(n+1)} f(i) = \\sum_{i \\in \\text{range } n} f(i) + f(n)$

  Then substitute the induction hypothesis for the remaining sum,
  and close with `ring`.

This **range-peel + IH** pattern is the foundation. In later levels,
when the algebra gets harder, you'll add `ring` to close the
inductive step — making it the full **range-peel + IH + ring**
workhorse pattern.

**Your task**: Prove that summing $1$ over `range n` gives $n$.
"

/-- `Finset.sum_range_zero` states that
`∑ k ∈ Finset.range 0, f k = 0`.

The sum over an empty range is zero (the identity for addition).

## Syntax
```
rw [Finset.sum_range_zero]
```

## When to use it
In the **base case** of a natural number induction proof about
sums over `Finset.range`. Since `range 0 = ∅`, the sum is 0.

## Connection
This is the range-based analogue of `Finset.sum_empty`.
Both say \"summing over nothing gives 0\" — `sum_range_zero`
is specialized to `range 0`, while `sum_empty` works for any `∅`.
-/
TheoremDoc Finset.sum_range_zero as "Finset.sum_range_zero" in "BigOp"

/-- The sum of 1 over `Finset.range n` equals `n`. -/
Statement (n : ℕ) : ∑ _i ∈ Finset.range n, (1 : ℕ) = n := by
  Hint "This is a natural number induction proof. Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: The sum over `range 0` is empty.
    Use `Finset.sum_range_zero` to rewrite."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]`."
    rw [Finset.sum_range_zero]
  | succ n ih =>
    Hint "**Inductive step**: Peel off the last term with
    `Finset.sum_range_succ`, then apply the IH."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]`."
    rw [Finset.sum_range_succ, ih]

Conclusion "
You proved $\\sum_{i=0}^{n-1} 1 = n$ by natural number induction.

**The pattern you used**:
1. `induction n with` — natural number induction (not finset induction)
2. Base case: `Finset.sum_range_zero` (sum over `range 0` is $0$)
3. Inductive step: `Finset.sum_range_succ` peels $f(n)$ off the top,
   then `ih` substitutes the known sum

This **range-peel + IH** pattern replaces the **insert-peel + IH**
pattern from FinsetInduction. Both work by decomposing a sum and
applying the IH, but range-peeling is natural when the sum is
indexed by consecutive integers $0, 1, \\ldots, n-1$.

In the next levels, you'll apply this pattern to classical formulas
where `ring` closes the algebra in the inductive step.
"

NewTheorem Finset.sum_range_zero

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.pow_eq_prod_const Finset.prod_const
