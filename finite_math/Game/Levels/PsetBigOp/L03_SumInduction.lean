import Game.Metadata

World "PsetBigOp"
Level 3

Title "Sum Induction: Additive Shift"

Introduction "
# Sum Induction: Shifting Every Term

Prove by finset induction:

$$\\sum_{x \\in s} (f(x) + 1) = \\sum_{x \\in s} f(x) + |s|$$

Each element contributes one extra unit, so the total increases by
the cardinality. The proof uses the same **collect-and-close**
pattern from FinsetInduction:

- **Base case**: both sums over $\\emptyset$ are $0$, and $|\\emptyset| = 0$
- **Inductive step**: peel both sums with `sum_insert ha`,
  peel cardinality with `card_insert_of_notMem ha`, apply the IH,
  and close with `omega`
"

/-- The sum of (f x + 1) over s equals the sum of f plus the cardinality. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ s, (f x + 1) = (∑ x ∈ s, f x) + s.card := by
  Hint (hidden := true) "Set up finset induction on `s`:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint (hidden := true) "Rewrite both sums and the cardinality:
    `rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]`"
    rw [Finset.sum_empty, Finset.sum_empty, Finset.card_empty]
    omega
  | @insert a s ha ih =>
    Hint (hidden := true) "Peel both sums and the cardinality:
    `rw [Finset.sum_insert ha, Finset.sum_insert ha,`
    `    Finset.card_insert_of_notMem ha, ih]`
    then `omega`."
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
        Finset.card_insert_of_notMem ha, ih]
    omega

Conclusion "
You proved $\\sum (f(x) + 1) = \\sum f(x) + |s|$ by finset induction.

This is the same collect-and-close pattern from FinsetInduction:
1. `sum_insert ha` peels the top element from each sum
2. `card_insert_of_notMem ha` peels the cardinality
3. `ih` substitutes the induction hypothesis
4. `omega` closes the resulting linear arithmetic

**Why not the algebraic approach?** You could also prove this with
`sum_add_distrib` and `sum_const`, decomposing the sum algebraically:
`sum_add_distrib` splits $\\sum (f(x) + 1)$ into $\\sum f(x) + \\sum 1$,
then `sum_const` rewrites $\\sum 1$ to $|s| \\cdot 1 = |s|$.

Both approaches are valid — the algebraic proof is shorter (two
rewrites vs. full induction), while the inductive proof works from
first principles without relying on the `sum_add_distrib` identity.
Choosing between them is a proof strategy decision: algebraic when
the right lemmas are available, inductive when you need to build
from the definition.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_add_distrib Finset.sum_const Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.card_eq_sum_ones
