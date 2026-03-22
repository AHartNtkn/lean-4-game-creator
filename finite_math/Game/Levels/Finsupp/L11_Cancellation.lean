import Game.Metadata

World "Finsupp"
Level 11

Title "Cancellation"

Introduction "
# Why Integer Values Matter

In Level 9 you saw that integer-valued Finsupp functions allow
negative coefficients. Now you will see the most important
consequence: **cancellation**.

If you add `single a b` and `single a (-b)`, the values at position
`a` are `b` and `-b`, which sum to zero. The entire function becomes
zero — not just at `a`, but as an element of `α →₀ ℤ`.

In polynomial language, this is the fact that `5x⁴ + (-5)x⁴ = 0`:
a monomial plus its negation cancels completely.

You will use two lemmas you already know:
1. `← Finsupp.single_add` to combine the two singles
2. `Finsupp.single_zero` to recognize `single a 0` as the zero function

**Your task**: Prove that `single 4 5 + single 4 (-5) = 0` in `ℕ →₀ ℤ`.
"

/-- Two singles at the same point with opposite values cancel to zero. -/
Statement : Finsupp.single 4 (5 : ℤ) + Finsupp.single 4 (-5) = 0 := by
  Hint "Combine the two singles into one using a backward rewrite.
  The lemma `← Finsupp.single_add` replaces
  `single a b₁ + single a b₂` with `single a (b₁ + b₂)`."
  Hint (hidden := true) "Try `rw [← Finsupp.single_add]`. This
  combines the two singles into `single 4 (5 + (-5))`, which
  simplifies to `single 4 0`."
  rw [← Finsupp.single_add]
  Hint "The goal is now `Finsupp.single 4 0 = 0`. You know from
  Level 4 that `single a 0` is the zero function."
  Hint (hidden := true) "Try `exact Finsupp.single_zero 4`."
  exact Finsupp.single_zero 4

Conclusion "
You have proved that `single 4 5 + single 4 (-5) = 0` — complete
cancellation. This is the algebraic reason that `ℤ` values (or any
type with negation) matter: they allow Finsupp functions to form a
**group** under addition, not just a monoid.

The proof combined two previously separate skills:
- `← single_add` to merge singles at the same position
- `single_zero` to recognize the zero function

In polynomial language: `5x⁴ + (-5)x⁴ = (5 + (-5))x⁴ = 0 · x⁴ = 0`.
The `single_add` step is the coefficient arithmetic, and `single_zero`
is the observation that a monomial with zero coefficient is the zero
polynomial.

This also shows why `support_single_ne_zero` requires the side
condition `b ≠ 0`: after cancellation, the support is empty even
though we started with two nonempty-support singles.
"

TheoremTab "Finsupp"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Finsupp.single_apply
