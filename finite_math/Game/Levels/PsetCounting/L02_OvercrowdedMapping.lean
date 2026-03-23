import Game.Metadata

World "PsetCounting"
Level 2

Title "Mapping Between Types"

Introduction "
You have a function `f : α → β` between two finite types, and
the source has strictly more elements than the target.

Prove that `f` cannot be injective.
"

/-- A function from a larger type to a smaller type cannot be injective. -/
Statement (α β : Type*) [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (hcard : Fintype.card β < Fintype.card α) :
    ¬ Function.Injective f := by
  Hint "The source is larger than the target, so some two
  distinct elements must map to the same output. Find those
  witnesses first, then use them to contradict injectivity."
  Hint (hidden := true) "Use `obtain ⟨a, b, hne, heq⟩ :=
  Fintype.exists_ne_map_eq_of_card_lt f hcard` to extract
  two distinct elements with the same image."
  obtain ⟨a, b, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  Hint (hidden := true) "Assume injectivity with `intro hinj`,
  then derive a contradiction: `exact hne (hinj heq)`."
  intro hinj
  exact hne (hinj heq)

Conclusion "
The size mismatch forces a collision: two distinct elements
map to the same output. Injectivity would require them to be
equal, contradicting their distinctness.

This is the pigeonhole principle: more pigeons than holes
means some hole has at least two pigeons.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.not_injective_of_card_lt Finset.exists_ne_map_eq_of_card_lt_of_maps_to
