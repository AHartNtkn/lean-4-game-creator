import Game.Metadata

World "PsetCounting"
Level 3

Title "Two Functions, One Target"

Introduction "
Two functions share a common codomain `β`:
- `f : α → β` is surjective (every element of `β` is hit)
- `g : γ → β` is injective (distinct inputs give distinct outputs)

What can you conclude about the sizes of `γ` and `α`?
Each function gives you a bound involving `Fintype.card β`.
Combine them.
"

/-- A surjection onto β and an injection into β constrain
the source sizes. -/
Statement (α β γ : Type*) [Fintype α] [Fintype β] [Fintype γ]
    (f : α → β) (g : γ → β)
    (hf : Function.Surjective f) (hg : Function.Injective g) :
    Fintype.card γ ≤ Fintype.card α := by
  Hint (hidden := true) "The surjection `f` gives a bound on
  `card β` relative to `card α`. Try
  `have h1 := Fintype.card_le_of_surjective f hf`."
  have h1 := Fintype.card_le_of_surjective f hf
  Hint (hidden := true) "The injection `g` gives a bound on
  `card γ` relative to `card β`. Try
  `have h2 := Fintype.card_le_of_injective g hg`."
  have h2 := Fintype.card_le_of_injective g hg
  Hint (hidden := true) "You have `card β ≤ card α` and
  `card γ ≤ card β`. Try `omega`."
  omega

Conclusion "
The surjection bound gives `card β ≤ card α`. The injection
bound gives `card γ ≤ card β`. Transitivity gives the result.

**Injection and surjection bounds are duals**: L02 showed that
too many source elements prevents injectivity (pigeonhole).
This level shows that surjectivity forces
`card target ≤ card source` (enough inputs to cover every
output). Both are consequences of the same size-constraint
principle:

| Property | Bound | Contrapositive |
|---|---|---|
| Injective | `card source ≤ card target` | more source than target prevents injectivity |
| Surjective | `card target ≤ card source` | more target than source prevents surjectivity |
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
