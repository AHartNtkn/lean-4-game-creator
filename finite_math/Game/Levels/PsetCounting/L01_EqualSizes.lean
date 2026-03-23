import Game.Metadata

World "PsetCounting"
Level 1

Title "Equal Type Sizes"

Introduction "
You are given an equivalence `e : Fin m ≃ Fin n` -- a perfect
pairing between elements of `Fin m` and elements of `Fin n`.

Prove that `m = n`.

This is **bijective counting**: the standard way to prove two
finite sets have equal size is to construct a bijection between
them, rather than counting each set independently. It is often
easier to find a structural pairing than to compute both
cardinalities.
"

/-- An equivalence between Fin m and Fin n forces m = n. -/
Statement (m n : ℕ) (e : Fin m ≃ Fin n) : m = n := by
  Hint (hidden := true) "An `Equiv` gives equal cardinalities
  via `Fintype.card_congr`. Try
  `have h := Fintype.card_congr e`."
  have h := Fintype.card_congr e
  Hint (hidden := true) "Try
  `rw [Fintype.card_fin, Fintype.card_fin] at h`."
  rw [Fintype.card_fin, Fintype.card_fin] at h
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`card_congr` converts a structural equivalence into a
cardinality equation. The `card_fin` rewrite evaluates
`Fintype.card (Fin k)` to `k`.

The converse also holds: `m = n` implies `Fin m ≃ Fin n`
(via `Fin.cast`). So `Fin n` faithfully represents
cardinality -- two `Fin` types are equivalent if and only
if their parameters are equal.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
