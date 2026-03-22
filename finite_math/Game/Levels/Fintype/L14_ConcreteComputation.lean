import Game.Metadata

World "Fintype"
Level 14

Title "Concrete Computation"

Introduction "
# Coached Practice: Closing with omega

When you use `card_*` lemmas on types with concrete numbers, the
rewrites reduce to pure arithmetic. For example, the cardinality of
`Bool → Fin 2 ⊕ Fin 3` is:

- Functions: `card (Fin 2 ⊕ Fin 3) ^ card Bool`
- Sum: `(card (Fin 2) + card (Fin 3)) ^ card Bool`
- Base types: `(2 + 3) ^ 2 = 5² = 25`

After all `card_*` rewrites, use `omega` to close the remaining
arithmetic goal.

**Your task**: Compute the number of functions from `Bool` to
`Fin 2 ⊕ Fin 3`.
"

/-- There are 25 functions from Bool to Fin 2 ⊕ Fin 3. -/
Statement : Fintype.card (Bool → Fin 2 ⊕ Fin 3) = 25 := by
  Hint "Start by decomposing the function type: `rw [Fintype.card_fun]`."
  rw [Fintype.card_fun]
  Hint "Now decompose the sum in the codomain: `rw [Fintype.card_sum]`."
  rw [Fintype.card_sum]
  Hint "Evaluate the base types: `rw [Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]`."
  Hint (hidden := true) "Try `rw [Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_bool, Fintype.card_fin, Fintype.card_fin]
  Hint "The goal is now arithmetic: `(2 + 3) ^ 2 = 25`. Use `omega`."
  omega

Conclusion "
You completed the decompose-evaluate-close workflow:

1. **Decompose**: use `card_fun`, `card_sum`, `card_prod` to break
   composite types into base types
2. **Evaluate**: use `card_fin`, `card_bool` to replace base types
   with numbers
3. **Close**: use `omega` for the remaining arithmetic

This is exactly the pattern you'll need for the boss — with the
addition of `card_congr` for the bijection step and
`card_subtype_compl` for complement counting.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
