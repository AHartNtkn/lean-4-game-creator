import Game.Metadata

World "CountingTypes"
Level 1

Title "Binary Strings"

Introduction "
# How Many Binary Strings of Length n?

A **binary string** of length `n` is a sequence of `n` bits, each
`true` or `false`. In type theory, this is exactly a function
`Fin n → Bool`: the domain `Fin n` indexes the `n` positions, and
the codomain `Bool` provides the two choices per position.

The exponentiation principle gives:

$$|\\text{Fin}\\;n \\to \\text{Bool}| = |\\text{Bool}|^{|\\text{Fin}\\;n|} = 2^n$$

For example, with $n = 3$ the 8 binary strings are:
`FFF, FFT, FTF, FTT, TFF, TFT, TTF, TTT`.

**Your task**: Prove this identity for a general `n` using `card_fun`,
`card_bool`, and `card_fin`.
"

/-- There are 2^n binary strings of length n. -/
Statement (n : ℕ) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  Hint "The goal involves a function type `Fin n → Bool`. What rule
  decomposes function types into base and exponent?"
  Hint (hidden := true) "Try `rw [Fintype.card_fun]`."
  rw [Fintype.card_fun]
  Hint "Now the goal has `Fintype.card Bool` and `Fintype.card (Fin n)`.
  Evaluate these base types to get concrete numbers."
  Hint (hidden := true) "Try `rw [Fintype.card_bool, Fintype.card_fin]`."
  rw [Fintype.card_bool, Fintype.card_fin]

Conclusion "
$$|\\text{Fin}\\;n \\to \\text{Bool}| = 2^n$$

Each function `Fin n → Bool` picks which of the `n` positions to mark
`true` — so the $2^n$ functions correspond to the $2^n$ subsets of an
`n`-element set.

This correspondence is not a coincidence — it's a **bijection**. Every
subset `S ⊆ Fin n` has a *characteristic function* `χ_S : Fin n → Bool`
that maps `i ↦ true` if `i ∈ S` and `i ↦ false` otherwise. Conversely,
every function `f : Fin n → Bool` determines a subset (its preimage of
`true`). This bijection is why `|powerset(S)| = 2^|S|` — the Powerset
world will formalize this connection.

**Workflow**: decompose with `card_fun`, evaluate base types with
`card_bool` and `card_fin`. When both sides match after rewriting,
the proof closes automatically. When concrete numbers remain (like
`2^3 = 8`), you'd use `omega` for the final arithmetic.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
