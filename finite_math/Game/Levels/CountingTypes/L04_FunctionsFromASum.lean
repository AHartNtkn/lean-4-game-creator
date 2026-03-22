import Game.Metadata

World "CountingTypes"
Level 4

Title "Functions from a Sum"

Introduction "
# Functions from a Disjoint Union

A function from a sum type `α ⊕ β → γ` is determined by its behavior
on the left component and the right component, independently. So:

$$|\\alpha \\oplus \\beta \\to \\gamma| = |\\gamma|^{|\\alpha| + |\\beta|}$$

For example, with `m = 2` and `n = 3`:
`Fin 2 ⊕ Fin 3 → Bool` has $2^{2+3} = 2^5 = 32$ elements.

**Your task**: Prove the general identity for `Fin m ⊕ Fin n → Bool`.
This combines `card_fun` with `card_sum` — the first time these two
appear together.
"

/-- There are 2^(m+n) functions from Fin m ⊕ Fin n to Bool. -/
Statement (m n : ℕ) : Fintype.card (Fin m ⊕ Fin n → Bool) = 2 ^ (m + n) := by
  Hint "The goal involves a function type. Decompose it first."
  Hint (hidden := true) "Try `rw [Fintype.card_fun]`."
  rw [Fintype.card_fun]
  Hint "The codomain and domain both need evaluating. The codomain is
  `Bool` and the domain is a sum type `Fin m ⊕ Fin n` — handle both."
  Hint (hidden := true) "Try `rw [Fintype.card_bool, Fintype.card_sum]`."
  rw [Fintype.card_bool, Fintype.card_sum]
  Hint "Evaluate the remaining `Fin` types to get concrete numbers."
  Hint (hidden := true) "Try `rw [Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_fin, Fintype.card_fin]

Conclusion "
$$|\\text{Fin}\\;m \\oplus \\text{Fin}\\;n \\to \\text{Bool}| = 2^{m+n}$$

A function from `Fin m ⊕ Fin n` to `Bool` is really **two independent
functions**: one from `Fin m → Bool` ($2^m$ choices) and one from
`Fin n → Bool` ($2^n$ choices). The total is $2^m \\times 2^n = 2^{m+n}$.

The type-theoretic identity behind this:

$$|\\alpha \\oplus \\beta \\to \\gamma| = |\\alpha \\to \\gamma| \\times |\\beta \\to \\gamma|$$

In cardinal arithmetic, $c^{a+b} = c^a \\cdot c^b$. The sum in the
exponent becomes a product — choosing independently from two groups
is the same as choosing from their union.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
