import Game.Metadata

World "SummationFormulas"
Level 4

Title "Sum of Squares"

Introduction "
# The Sum of Squares Formula

The next classical formula after the Gauss sum is the **sum of squares**:

$$\\sum_{i=0}^{n} i^2 = \\frac{n(n+1)(2n+1)}{6}$$

As with the Gauss sum, we avoid natural number division by multiplying
both sides by $6$:

$$6 \\cdot \\sum_{i=0}^{n} i^2 = n \\cdot (n+1) \\cdot (2n+1)$$

**The proof** follows the same pattern as the Gauss sum (Level 2):
peel with `sum_range_succ`, distribute with `mul_add`, substitute
the IH, and close with `ring`. The algebra in the inductive step
is heavier, but `ring` handles it all.
"

/-- Six times the sum of squares from 0 to n equals n(n+1)(2n+1). -/
Statement (n : ℕ) : 6 * (∑ i ∈ Finset.range (n + 1), i ^ 2) = n * (n + 1) * (2 * n + 1) := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: You've done this pattern twice. Try it yourself."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Finset.sum_range_zero]`
    then `ring`."
    rw [Finset.sum_range_succ, Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Same pattern as Level 2.
    Peel, distribute, substitute, close."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, mul_add, ih]`
    then `ring`."
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

Conclusion "
You proved the sum-of-squares formula:
$$6\\sum_{i=0}^{n} i^2 = n(n+1)(2n+1)$$

Together with the Gauss sum, this completes two of the three classical
power-sum formulas. The third — $\\sum i^3 = (\\sum i)^2$ — is another
beautiful identity you could prove with the same technique.

**Pattern reinforcement**: This level used exactly the Gauss sum
pattern: peel, `mul_add`, IH, `ring`. The `mul_add` step is needed
whenever a constant multiplier (here $6$) wraps the sum — it
separates the sum (which the IH knows about) from the new term.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.pow_eq_prod_const Finset.prod_const
