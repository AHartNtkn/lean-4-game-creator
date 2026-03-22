import Game.Metadata

World "SummationFormulas"
Level 3

Title "Sum of Odd Numbers"

Introduction "
# The Sum of the First $n$ Odd Numbers

Here is a beautiful identity:

$$\\sum_{i=0}^{n-1} (2i + 1) = n^2$$

The first $n$ odd numbers — $1, 3, 5, 7, \\ldots, (2n-1)$ — sum to a
perfect square. Geometrically, you can see this by building an
$n \\times n$ square one L-shaped layer at a time: the first layer
has 1 cell, the second has 3, the third has 5, and so on.

**The proof** follows the standard range-peel + IH + ring pattern.
This time, `ring` handles the entire inductive step without needing
`mul_add` — the goal after peeling and substituting is a pure
polynomial identity.
"

/-- The sum of the first n odd numbers equals n squared. -/
Statement (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  Hint "Induct on `n`."
  Hint (hidden := true) "Type:
  `induction n with`
  `| zero => sorry`
  `| succ n ih => sorry`"
  induction n with
  | zero =>
    Hint "**Base case**: Simplify `range 0` and close."
    Hint (hidden := true) "Try `rw [Finset.sum_range_zero]` then `ring`."
    rw [Finset.sum_range_zero]
    ring
  | succ n ih =>
    Hint "**Inductive step**: Peel, substitute, close.
    You've done this pattern twice now — try it in one shot."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, ih]` then `ring`."
    rw [Finset.sum_range_succ, ih]
    Hint "After substitution, the goal is:
    `n ^ 2 + (2 * n + 1) = (n + 1) ^ 2`.
    This is the algebraic identity $(n+1)^2 = n^2 + 2n + 1$."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved that $1 + 3 + 5 + \\cdots + (2n-1) = n^2$.

Notice how clean this proof is compared to the Gauss sum. The
key difference: after `rw [sum_range_succ, ih]`, the goal was
$n^2 + (2n + 1) = (n+1)^2$, which is a **polynomial identity**.
`ring` closes polynomial identities directly — no need for
`mul_add` or other intermediate steps.

**When do you need `mul_add`?** Only when the IH is buried inside
a product (like $2 \\cdot (\\Sigma + k)$). When the IH appears
additively, `rw [ih]` substitutes directly and `ring` handles the rest.

**Geometric insight**: each odd number $2i+1$ forms an L-shaped
gnomon around the previous $i \\times i$ square, extending it to
$(i+1) \\times (i+1)$. Your inductive step captures exactly this
geometric argument.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.mul_sum Finset.sum_mul Finset.sum_range_sub Finset.eq_sum_range_sub Finset.sum_range_id_mul_two Finset.sum_range_id Finset.pow_eq_prod_const Finset.prod_const
