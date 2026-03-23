import Game.Metadata

World "PsetCounting"
Level 6

Title "The Indirect Path"

Introduction "
You have two functions `f : α → β` and `g : β → γ`, where:
- `f` is surjective
- The composition `g ∘ f` is injective

Prove that `Fintype.card β ≤ Fintype.card γ`.

Neither hypothesis alone gives the bound you need directly.
Think about what each one tells you about cardinalities, and
find a path from `card β` to `card γ`.
"

/-- If f is surjective and g ∘ f is injective,
then card β ≤ card γ. -/
Statement (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : β → γ)
    (hf : Function.Surjective f) (hcomp : Function.Injective (g ∘ f)) :
    Fintype.card β ≤ Fintype.card γ := by
  Hint (hidden := true) "The composition `g ∘ f` is injective.
  What bound does `card_le_of_injective` give you?
  Try `have h1 := Fintype.card_le_of_injective (g ∘ f) hcomp`."
  have h1 := Fintype.card_le_of_injective (g ∘ f) hcomp
  Hint (hidden := true) "The surjection `f` bounds `card β` by
  `card α`. Try
  `have h2 := Fintype.card_le_of_surjective f hf`."
  have h2 := Fintype.card_le_of_surjective f hf
  Hint (hidden := true) "You have `card α ≤ card γ` and
  `card β ≤ card α`. Try `omega`."
  omega

Conclusion "
Neither hypothesis directly relates `card β` to `card γ`.
The surjection `f` gives `card β ≤ card α`, and the injective
composition gives `card α ≤ card γ`. Chaining through the
intermediate type `α` produces the result.

This is a **technique selection** problem: the hypotheses
don't signal which counting tool to use. You had to recognize
that the injection bound applies to the *composition* (not to
`f` or `g` individually) and that the surjection bound on `f`
provides the missing link.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
