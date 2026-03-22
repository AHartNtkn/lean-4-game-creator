import Game.Metadata

World "PsetBigOp"
Level 6

Title "Product Induction: Pulling Out a Constant"

Introduction "
# Pulling a Constant Out of a Product

Prove that multiplying each factor by $2$ scales the entire product
by $2^{|s|}$:

$$\\prod_{x \\in s} (2 \\cdot f(x)) = 2^{|s|} \\cdot \\prod_{x \\in s} f(x)$$

This is a product identity proved by **finset induction**. The
collect-and-close pattern from FinsetInduction applies to products
just as it does to sums:

- **Base case**: both products over $\\emptyset$ are $1$, and $2^0 = 1$
- **Inductive step**: peel both products with `prod_insert ha`,
  peel cardinality with `card_insert_of_notMem ha`, apply the IH,
  and close with `ring`
"

/-- Pulling a constant factor out of a product. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∏ x ∈ s, (2 * f x) = 2 ^ s.card * ∏ x ∈ s, f x := by
  Hint (hidden := true) "Set up finset induction on `s`:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint (hidden := true) "Rewrite both products with `prod_empty` and
    the cardinality with `card_empty`, then `ring`."
    rw [Finset.prod_empty, Finset.prod_empty, Finset.card_empty]
    ring
  | @insert a s ha ih =>
    Hint (hidden := true) "Peel both products and the cardinality:
    `rw [Finset.prod_insert ha, Finset.prod_insert ha,`
    `    Finset.card_insert_of_notMem ha, ih]`
    then `ring`."
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.card_insert_of_notMem ha, ih]
    ring

Conclusion "
You proved that a constant factor can be pulled out of a product:
$$\\prod (2 \\cdot f) = 2^{|s|} \\cdot \\prod f$$

The proof used the same **collect-and-close** pattern as sum
induction — the only differences are `prod_insert` instead of
`sum_insert`, and `ring` handling the multiplicative algebra
(including $2^{|s|+1} = 2 \\cdot 2^{|s|}$).
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.prod_const Finset.pow_eq_prod_const Finset.prod_mul_distrib
