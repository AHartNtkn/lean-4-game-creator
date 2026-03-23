import Game.Metadata

World "PsetCounting"
Level 7

Title "Two Functions, Two Steps"

Introduction "
You have two functions:
- `f : α → β` is injective, with `Fintype.card β = 5`
- `g : Fin 11 → α`

Prove that two inputs to `g` produce the same output.
"

/-- An injection constrains the source size, creating a collision
in a second function. -/
Statement (α β : Type*) [Fintype α] [Fintype β] [DecidableEq α]
    (f : α → β) (g : Fin 11 → α)
    (hinj : Function.Injective f)
    (hβ : Fintype.card β = 5) :
    ∃ a b : Fin 11, a ≠ b ∧ g a = g b := by
  Hint "One function constrains a type's size. Use that
  constraint to trigger a counting argument on the other
  function."
  Hint (hidden := true) "What does the injection `f` tell you
  about `card α`? Try
  `have h := Fintype.card_le_of_injective f hinj`."
  have h := Fintype.card_le_of_injective f hinj
  Hint (hidden := true) "Try
  `apply Fintype.exists_ne_map_eq_of_card_lt`."
  apply Fintype.exists_ne_map_eq_of_card_lt
  Hint (hidden := true) "Try `rw [Fintype.card_fin]` then
  `omega`."
  rw [Fintype.card_fin]
  omega

Conclusion "
Neither function alone determines the answer. The injection
bound on `f` constrains `card α`, and that constraint makes
`g` a collision situation.

This is the **information chaining** strategy: use one
function's property to constrain a type's cardinality, then
use that constraint to trigger a different counting technique
on a second function. The boss requires exactly this pattern
-- an injection constrains one type, and that constraint
feeds into a fiber decomposition on another function.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Fintype.not_injective_of_card_lt Finset.exists_ne_map_eq_of_card_lt_of_maps_to
