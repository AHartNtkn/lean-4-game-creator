import Game.Metadata

World "FinsetInduction"
Level 7

Title "Product Induction"

Introduction "
# Induction with Products

Everything you've learned about finset induction for sums transfers
directly to **products**. The structure is identical:

- **Base case**: `Finset.prod_empty` gives
  $\\prod_{x \\in \\emptyset} f(x) = 1$

  The empty product is $1$ (the multiplicative identity), just as
  the empty sum is $0$ (the additive identity).

- **Inductive step**: `Finset.prod_insert ha` gives
  $\\prod_{x \\in \\text{insert } a\\ s} f(x) = f(a) \\cdot \\prod_{x \\in s} f(x)$

The proof pattern is the same **peel-IH-ring** recipe:
1. Peel with `prod_insert ha`
2. Apply the IH
3. Close with `ring`

**Your task**: Prove that the product of $1$ over any finset is $1$.
This is the product analogue of L01's 'sum of 0 = 0'.
"

/-- The product of 1 over any finset is 1, proved by finset induction. -/
Statement (s : Finset ℕ) : ∏ _x ∈ s, (1 : ℕ) = 1 := by
  Hint "Start with finset induction on `s`, just as you did for sums."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: The goal is `∏ x ∈ ∅, 1 = 1`.
    Use `Finset.prod_empty` — the product analogue of `sum_empty`.
    Where `sum_empty` gives $0$, `prod_empty` gives $1$."
    Hint (hidden := true) "Try `rw [Finset.prod_empty]`."
    rw [Finset.prod_empty]
  | @insert a s ha ih =>
    Hint "**Inductive step**: Use `Finset.prod_insert ha` to peel
    the product over `insert a s` into `f(a) * ∏ x ∈ s, f(x)`.
    Then apply the IH and close."
    Hint (hidden := true) "Try `rw [Finset.prod_insert ha, ih]`
    then `ring`."
    rw [Finset.prod_insert ha, ih]
    ring

Conclusion "
Product induction follows the exact same pattern as sum induction:

| Operation | Base lemma | Base value | Peel lemma |
|-----------|------------|------------|------------|
| Sum (`∑`) | `sum_empty` | `0` | `sum_insert ha` |
| Product (`∏`) | `prod_empty` | `1` | `prod_insert ha` |

The key difference: the empty product is $1$ (the multiplicative
identity), not $0$. This makes sense — multiplying by the identity
element shouldn't change anything, and for multiplication that
element is $1$.

In the next level, you'll use product induction on a more
interesting identity.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub
