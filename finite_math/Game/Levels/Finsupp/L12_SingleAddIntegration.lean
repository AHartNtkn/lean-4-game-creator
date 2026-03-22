import Game.Metadata

World "Finsupp"
Level 12

Title "Combining Algebra and Support"

Introduction "
# Using `single_add` with Support Reasoning

In the last level you learned that `Finsupp.single_add` lets you
combine two singles at the same point into one:

`Finsupp.single a b₁ + Finsupp.single a b₂ = Finsupp.single a (b₁ + b₂)`

Now let's use that algebraic identity for something practical:
proving a fact about the **support** of a sum of singles.

If you can combine two singles into one using `← single_add`, you
reduce the sum to a single `Finsupp.single` whose support you already
know how to compute with `support_single_ne_zero`.

**Your task**: Prove that the support of
`Finsupp.single 5 3 + Finsupp.single 5 4` is the singleton
containing `5`.
"

/-- Combine two singles algebraically, then compute the support. -/
Statement : (Finsupp.single 5 3 + Finsupp.single 5 4 : ℕ →₀ ℕ).support = {5} := by
  Hint "First, combine the two singles into one using a backward
  rewrite with `single_add`."
  Hint (hidden := true) "Try `rw [← Finsupp.single_add]`. This
  combines `single 5 3 + single 5 4` into `single 5 (3 + 4)`,
  which is `single 5 7`."
  rw [← Finsupp.single_add]
  Hint "Now the goal is `(Finsupp.single 5 7).support = ...`.
  Use `support_single_ne_zero` to compute the support."
  Hint (hidden := true) "Try `apply Finsupp.support_single_ne_zero`.
  This leaves the goal `7 ≠ 0`."
  apply Finsupp.support_single_ne_zero
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
This is the power of algebraic reasoning with `single_add`: instead
of evaluating the sum pointwise at every position (which you did in
Level 9), you can *simplify the expression first* and then reason
about the simpler form.

The two-step pattern:
1. `rw [← Finsupp.single_add]` — combine singles at the same point
2. `apply Finsupp.support_single_ne_zero` — compute the support

This is exactly how you reason about polynomials: first simplify
`3x⁵ + 4x⁵ = 7x⁵`, then observe that `7x⁵` has one nonzero term
at degree `5`.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
