import Game.Metadata

World "PsetCardinality"
Level 8

Title "Function Type Cardinality"

Introduction "
# Counting Functions from an Abstract Domain

Given an abstract type `α` equivalent to `Fin 2 ⊕ Bool`, count the
functions from `α` to `Fin 3`:

$$|\\alpha \\to \\text{Fin}\\;3| = |\\text{Fin}\\;3|^{|\\alpha|} = 3^{|\\text{Fin}\\;2 \\oplus \\text{Bool}|} = 3^{2+2} = 3^4 = 81$$

This retrieves the function-type cardinality formula from the
Fintype world, combined with equivalence resolution to handle
the abstract domain and sum-type decomposition.
"

/-- The cardinality of (α → Fin 3) is 81, given α ≃ Fin 2 ⊕ Bool. -/
Statement (α : Type*) [Fintype α] [DecidableEq α] (e : α ≃ Fin 2 ⊕ Bool) :
    Fintype.card (α → Fin 3) = 81 := by
  Hint "Decompose the function type into base and exponent, resolve
  the abstract domain, then evaluate each piece."
  Hint (hidden := true) "You need (in order): `card_fun`, `card_congr e`,
  `card_sum`, `card_fin`, `card_bool`, `card_fin` — then `omega` for the final arithmetic."
  Hint (hidden := true) "Full proof:
  `rw [Fintype.card_fun, Fintype.card_congr e, Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]`
  `omega`"
  rw [Fintype.card_fun]
  Hint (hidden := true) "The goal is `Fintype.card (Fin 3) ^ Fintype.card α = 81`.
  Resolve α via `rw [Fintype.card_congr e]`."
  rw [Fintype.card_congr e]
  Hint (hidden := true) "The exponent is `Fintype.card (Fin 2 ⊕ Bool)`.
  Decompose the sum type: `rw [Fintype.card_sum]`."
  rw [Fintype.card_sum]
  Hint (hidden := true) "Now evaluate each component type:
  `rw [Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]`."
  rw [Fintype.card_fin, Fintype.card_bool, Fintype.card_fin]
  Hint (hidden := true) "The goal is `3 ^ (2 + 2) = 81`. `omega` closes it."
  omega

Conclusion "
$$|\\alpha \\to \\text{Fin}\\;3| = 3^{|\\alpha|} = 3^{|\\text{Fin}\\;2 \\oplus \\text{Bool}|} = 3^{2+2} = 81$$

The decompose-evaluate workflow with a twist — the abstract type
appears in the **exponent** (domain of the function), not in the
base (codomain):

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_fun` | split: $|\\text{Fin}\\;3|^{|\\alpha|}$ |
| 2 | `card_congr e` | resolve domain: $|\\text{Fin}\\;2 \\oplus \\text{Bool}|$ |
| 3 | `card_sum` | decompose: $|\\text{Fin}\\;2| + |\\text{Bool}|$ |
| 4-5 | `card_fin`, `card_bool` | evaluate: $3^{2+2}$ |
| 6 | `omega` | close: $3^4 = 81$ |

In the Fintype world, `card_fun` was applied to concrete types.
Here the abstract domain makes `card_congr` necessary — the same
pattern as L09's complement and L10's injections, but applied to
function types.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
