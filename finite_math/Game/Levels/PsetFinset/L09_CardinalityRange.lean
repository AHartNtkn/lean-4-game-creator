import Game.Metadata

World "PsetFinset"
Level 9

Title "Cardinality of an Injective Image"

Introduction "
# Cardinality + Range Integration

If $f$ is injective, the image of `Finset.range n` has exactly $n$
elements.

This retrieves two tools:
- `Finset.card_image_of_injective` from FinsetImage: injective functions
  preserve the number of elements
- `Finset.card_range`: `(Finset.range n).card = n`

The bridge: `Finset.range n` contains $\\{0, 1, \\ldots, n-1\\}$ — the
same values that `Fin n` represents. Its cardinality is $n$.
"

/-- The image of range n under an injective function has exactly n elements. -/
Statement (f : ℕ → ℕ) (hf : Function.Injective f) (n : ℕ) :
    ((Finset.range n).image f).card = n := by
  Hint "What does `card_image_of_injective` tell you about the left side?"
  Hint (hidden := true) "Use
  `have h := Finset.card_image_of_injective (Finset.range n) hf`
  to get `((Finset.range n).image f).card = (Finset.range n).card`.
  Then `rw [Finset.card_range] at h` simplifies to `... = n`."
  have h := Finset.card_image_of_injective (Finset.range n) hf
  rw [Finset.card_range] at h
  exact h

Conclusion "
Two facts combined:
1. `card_image_of_injective`: $|f(S)| = |S|$ when $f$ is injective
2. `card_range`: $|\\{0, \\ldots, n-1\\}| = n$

`Finset.card_range` is the cardinality form of the **Fin-Finset bridge**:
`Finset.range n` contains the same values as `Fin n`, so its cardinality
is $n$.

**Note**: You're using `card_range` here as a preview — the Cardinality
world will place it in the broader context of the card_* lemma family.
"

/-- `Finset.card_range n` states that `(Finset.range n).card = n`:
the range containing 0 through n-1 has exactly n elements. -/
TheoremDoc Finset.card_range as "Finset.card_range" in "Finset"

NewTheorem Finset.card_range

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg linarith
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_image_of_mem Finset.image_subset_image Finset.image_mono
