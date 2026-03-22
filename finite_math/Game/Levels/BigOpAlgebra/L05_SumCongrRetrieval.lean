import Game.Metadata

World "BigOpAlgebra"
Level 5

Title "Recognizing Constant Functions"

Introduction "
# Combining sum_congr and sum_const

Sometimes a function isn't *syntactically* constant, but you
know from hypotheses that it evaluates to the same value on
every element of the finset.

You learned `Finset.sum_congr` in BigOpIntro:
```
Finset.sum_congr (h₁ : s₁ = s₂) (h₂ : ∀ x ∈ s₂, f x = g x) :
  ∑ x ∈ s₁, f x = ∑ x ∈ s₂, g x
```

Combined with `sum_const`, this gives a two-step strategy:
1. Use `sum_congr` to rewrite the summand to a constant
2. Use `sum_const` to evaluate the constant sum

**Your task**: Given that `f x = c` for all `x ∈ s`, prove
`∑ x ∈ s, f x = s.card • c`.
"

/-- When f is constant on s, the sum equals card • c. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (c : ℕ)
    (h : ∀ x ∈ s, f x = c) :
    ∑ x ∈ s, f x = s.card • c := by
  Hint "Use `rw [Finset.sum_congr rfl h]` to rewrite the summand.
  Here `rfl` says the finset doesn't change, and `h` says each
  `f x` becomes `c`."
  Hint (hidden := true) "Try `rw [Finset.sum_congr rfl h]` — this
  rewrites `∑ x ∈ s, f x` to `∑ x ∈ s, c`."
  rw [Finset.sum_congr rfl h]
  Hint "Now the sum is constant. Use `exact Finset.sum_const c` —
  note the explicit argument `c`."
  Hint (hidden := true) "Try `exact Finset.sum_const c`."
  exact Finset.sum_const c

Conclusion "
The `sum_congr` + `sum_const` combination is a common pattern:
first normalize the summand, then evaluate.

This is also your first use of `exact` with an **explicit
argument**: `exact Finset.sum_const c`. Lean can't infer `c`
from context when using `exact`, so you must provide it. You'll
see this pattern whenever a theorem has arguments that can't be
determined from the goal alone.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
