import Game.Metadata

World "BigOpIntro"
Level 11

Title "Counting via Summation"

Introduction "
# The Bridge in Action

You just learned that `s.card = ∑ x ∈ s, 1` — cardinality is
summation of the constant function 1.

Now use this bridge in combination with `sum_congr`. If every
element contributes `1` to a sum, the sum equals the cardinality.
This connects two tools you know: pointwise rewriting and the
card-sum bridge.

**Your task**: Given that `f x = 1` for all `x ∈ s`, prove that
summing `f` over `s` gives `s.card`.
"

/-- If f is identically 1 on s, the sum of f over s equals the cardinality. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∀ x ∈ s, f x = 1) :
    ∑ x ∈ s, f x = s.card := by
  Hint "First use `sum_congr` to replace `f` with the constant
  function 1 inside the sum."
  Hint (hidden := true) "Try:
  `have hsimp : ∑ x ∈ s, f x = ∑ x ∈ s, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hf x hx`
  Then `rw [hsimp]`."
  have hsimp : ∑ x ∈ s, f x = ∑ x ∈ s, 1 := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hf x hx
  rw [hsimp]
  Hint "Now the goal is `∑ x ∈ s, 1 = s.card`. Use the reverse
  direction of `card_eq_sum_ones` to rewrite `∑ x ∈ s, 1` back
  to `s.card`."
  Hint (hidden := true) "Try `rw [← Finset.card_eq_sum_ones]`."
  rw [← Finset.card_eq_sum_ones]

Conclusion "
You've used two tools in combination:
1. **sum_congr** to replace `f` with the constant `1`
2. **card_eq_sum_ones** (in reverse) to connect `∑ 1` back to `card`

This pattern — rewriting a sum into a cardinality or vice versa —
is the practical payoff of the card-sum bridge. Whenever you see
a sum of a constant function, you can convert it to a cardinality
problem, and conversely.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.sum_pair Finset.prod_pair
