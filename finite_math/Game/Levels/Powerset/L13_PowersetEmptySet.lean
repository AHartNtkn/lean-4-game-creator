import Game.Metadata

World "Powerset"
Level 13

Title "The Powerset of the Empty Set"

Introduction "
# Edge Case: 2^0 = 1

The empty set has exactly one subset: itself. So its powerset
has one element. This is the edge case $2^0 = 1$ for the
powerset cardinality formula.

**Your task**: Prove `((∅ : Finset ℕ).powerset).card = 1`.

This uses `card_powerset` (from Level 12) together with
`Finset.card_empty` (from Cardinality). The `have` pattern
lets Lean compute $2^0 = 1$ automatically.
"

/-- The powerset of the empty set has exactly one element. -/
Statement : ((∅ : Finset ℕ).powerset).card = 1 := by
  Hint "Use `have` to bring `card_powerset` into the context,
  applied to the empty finset."
  Hint (hidden := true) "Try `have h := Finset.card_powerset (∅ : Finset ℕ)`."
  have h := Finset.card_powerset (∅ : Finset ℕ)
  Hint "Now `h : ((∅ : Finset ℕ).powerset).card = 2 ^ (∅ : Finset ℕ).card`.
  Use `Finset.card_empty` to replace `(∅ : Finset ℕ).card` with `0`."
  Hint (hidden := true) "Try `rw [Finset.card_empty] at h`."
  rw [Finset.card_empty] at h
  Hint "Now `h` says the count equals `2 ^ 0`, which Lean reduces
  to `1`. The hypothesis matches the goal."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Three steps: `have h := card_powerset ∅`, `rw [card_empty] at h`, `exact h`.

The powerset of `∅` is the set containing only `∅` itself — one element.
This matches the formula: $2^0 = 1$.

Why does this matter? The convention $2^0 = 1$ sometimes feels
arbitrary in algebra. Here it has a concrete meaning: there is
exactly one way to choose a subset of nothing — choose nothing.
This is the same reasoning behind $0! = 1$ and $\\binom{0}{0} = 1$.

This level retrieved `card_powerset` from Level 12 and combined
it with `card_empty` from the Cardinality world — the pattern
of chaining a structure lemma with a known value.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
