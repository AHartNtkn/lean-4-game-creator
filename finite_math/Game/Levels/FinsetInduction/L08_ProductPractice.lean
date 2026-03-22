import Game.Metadata

World "FinsetInduction"
Level 8

Title "Product Distributivity by Induction"

Introduction "
# Proving a Product Identity

Now use product induction on a real identity. You'll prove:

$$\\prod_{x \\in s} (f(x) \\cdot g(x)) = \\Bigl(\\prod_{x \\in s} f(x)\\Bigr) \\cdot \\Bigl(\\prod_{x \\in s} g(x)\\Bigr)$$

This says: the product of pointwise products equals the product of
the products. It's the multiplicative analogue of `sum_add_distrib`.

**The proof plan** (peel-IH-ring for products):
- **Base case**: three `prod_empty` rewrites, then `ring`
- **Inductive step**: three `prod_insert ha` rewrites, then `ih`,
  then `ring`
"

/-- Product distributes over pointwise multiplication. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ) :
    ∏ x ∈ s, (f x * g x) = (∏ x ∈ s, f x) * (∏ x ∈ s, g x) := by
  Hint "Start with finset induction on `s`."
  Hint (hidden := true) "Type:
  `induction s using Finset.induction_on with`
  `| empty => sorry`
  `| @insert a s ha ih => sorry`"
  induction s using Finset.induction_on with
  | empty =>
    Hint "**Base case**: Rewrite all three products over `∅` to `1`,
    then close the arithmetic `1 = 1 * 1`."
    Hint (hidden := true) "Try
    `rw [Finset.prod_empty, Finset.prod_empty, Finset.prod_empty]`
    then `ring`."
    rw [Finset.prod_empty, Finset.prod_empty, Finset.prod_empty]
    ring
  | @insert a s ha ih =>
    Hint "**Inductive step**: Peel all three products with
    `prod_insert ha`, apply the IH, then close with `ring`.

    You need three peels — one for each `∏` in the equation."
    Hint (hidden := true) "Try:
    `rw [Finset.prod_insert ha, Finset.prod_insert ha,`
    `    Finset.prod_insert ha, ih]`
    then `ring`."
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.prod_insert ha, ih]
    Hint "The goal is now:
    `f a * g a * (∏ f * ∏ g) = (f a * ∏ f) * (g a * ∏ g)`.
    This is pure algebra — rearranging factors. `ring` closes it."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You've proved that products distribute over pointwise multiplication
— entirely by induction!

The product version of peel-IH-ring works exactly like the sum
version:

| Sum version | Product version |
|-------------|-----------------|
| `sum_empty` (gives `0`) | `prod_empty` (gives `1`) |
| `sum_insert ha` | `prod_insert ha` |
| `rw [ih]` | `rw [ih]` |
| `ring` | `ring` |

The algebra in the inductive step is different (rearranging factors
rather than collecting terms), but `ring` handles both.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul Finset.sum_const Finset.card_eq_sum_ones Finset.sum_add_distrib Finset.prod_mul_distrib Finset.prod_const_one Finset.prod_eq_one Finset.sum_range_sub Finset.eq_sum_range_sub
