import Game.Metadata

World "PsetBigOp"
Level 7

Title "Calc Chain: Sum-Product Decomposition"

Introduction "
# Organizing a Mixed Sum-Product Proof

Prove:

$$\\Bigl(\\sum_{x \\in s} (f(x) + g(x))\\Bigr) \\cdot \\Bigl(\\prod_{x \\in s} (f(x) \\cdot g(x))\\Bigr) = 360$$

This combines **additive** and **multiplicative** decomposition
in a single proof. A `calc` chain organizes the steps clearly:

1. Split the sum with `sum_add_distrib` and the product with
   `prod_mul_distrib`
2. Substitute the four known values
3. Close the arithmetic with `ring`

You can also solve this with chained `rw` if you prefer — both
approaches are valid.
"

/-- Combine sum_add_distrib and prod_mul_distrib in a calc chain. -/
Statement (s : Finset ℕ) (f g : ℕ → ℕ)
    (hfsum : ∑ x ∈ s, f x = 10) (hgsum : ∑ x ∈ s, g x = 5)
    (hfprod : ∏ x ∈ s, f x = 6) (hgprod : ∏ x ∈ s, g x = 4) :
    (∑ x ∈ s, (f x + g x)) * (∏ x ∈ s, (f x * g x)) = 360 := by
  Hint "Split the sum with `Finset.sum_add_distrib` and the product
  with `Finset.prod_mul_distrib`, then substitute the four hypotheses
  and close with `ring`. You can use either a `calc` chain or a
  sequence of `rw` steps."
  Hint (hidden := true) "Start a `calc` chain:
  `calc (∑ x ∈ s, (f x + g x)) * (∏ x ∈ s, (f x * g x))`
  `    = ((∑ x ∈ s, f x) + ∑ x ∈ s, g x) * ((∏ x ∈ s, f x) * ∏ x ∈ s, g x) := by`
  `      rw [Finset.sum_add_distrib, Finset.prod_mul_distrib]`
  `  _ = (10 + 5) * (6 * 4) := by rw [hfsum, hgsum, hfprod, hgprod]`
  `  _ = 360 := by ring`"
  Branch
    rw [Finset.sum_add_distrib, Finset.prod_mul_distrib,
        hfsum, hgsum, hfprod, hgprod]
    ring
  Branch
    rw [Finset.sum_add_distrib, Finset.prod_mul_distrib]
    Hint (hidden := true) "Substitute the known values:
    `rw [hfsum, hgsum, hfprod, hgprod]` then `ring`."
    rw [hfsum, hgsum, hfprod, hgprod]
    ring
  calc (∑ x ∈ s, (f x + g x)) * (∏ x ∈ s, (f x * g x))
      = ((∑ x ∈ s, f x) + ∑ x ∈ s, g x) *
        ((∏ x ∈ s, f x) * ∏ x ∈ s, g x) := by
        rw [Finset.sum_add_distrib, Finset.prod_mul_distrib]
    _ = (10 + 5) * (6 * 4) := by rw [hfsum, hgsum, hfprod, hgprod]
    _ = 360 := by ring

Conclusion "
You decomposed a mixed sum-product expression:
1. `sum_add_distrib` split the sum: $\\sum(f + g) = \\sum f + \\sum g$
2. `prod_mul_distrib` split the product: $\\prod(f \\cdot g) = \\prod f \\cdot \\prod g$
3. Substitution + `ring` closed the arithmetic

**`calc` vs `rw`**: Both work here. `calc` makes each intermediate
expression explicit — useful when you want to check your algebra.
`rw` chains are more compact. For proofs with 3+ steps or mixed
justifications, `calc` is usually clearer.

**Sum-product duality**: `sum_add_distrib` and `prod_mul_distrib`
are twins — one additive, one multiplicative. Whenever you see
a pointwise operation ($f + g$ or $f \\cdot g$) inside a big
operator, the corresponding distributivity lemma splits it.
"

TheoremTab "BigOp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.sum_pair Finset.prod_pair
