import Game.Metadata

World "Fintype"
Level 9

Title "Combining Subtype and Product"

Introduction "
# Practice: Complement Counting + Products

You learned `card_subtype_compl` in the last level. Now combine it
with `card_prod` to compute the cardinality of a product involving
a complement subtype.

Given a finite type `α` with 12 elements and a predicate `P` with
4 elements satisfying it, the complement `{x // ¬P x}` has
`12 - 4 = 8` elements. Taking the product with `Fin 3` gives
`8 * 3 = 24` elements.

**Your task**: Decompose using `card_prod`, then apply `card_subtype_compl`,
then substitute the known values.
"

/-- If α has 12 elements and 4 satisfy P, then {x // ¬P x} × Fin 3 has 24 elements. -/
Statement (α : Type*) [Fintype α] (P : α → Prop) [DecidablePred P]
    [Fintype { x // P x }] [Fintype { x // ¬P x }]
    (hα : Fintype.card α = 12) (hp : Fintype.card { x // P x } = 4) :
    Fintype.card ({ x // ¬P x } × Fin 3) = 24 := by
  Hint "Start by decomposing the product: `rw [Fintype.card_prod]`."
  rw [Fintype.card_prod]
  Hint "Now apply complement counting for the subtype:
  `rw [Fintype.card_subtype_compl]`."
  rw [Fintype.card_subtype_compl]
  Hint "Substitute the known values: `rw [hα, hp, Fintype.card_fin]`."
  Hint (hidden := true) "Try `rw [hα, hp, Fintype.card_fin]`."
  rw [hα, hp, Fintype.card_fin]

Conclusion "
You combined two composition rules in a single proof:

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_prod` | `card (¬P × Fin 3) → card (¬P) * card (Fin 3)` |
| 2 | `card_subtype_compl` | `→ (card α - card P) * card (Fin 3)` |
| 3 | `hα`, `hp`, `card_fin` | `→ (12 - 4) * 3 = 24` |

This is the complement counting workflow: instead of counting elements
that satisfy a predicate directly, compute the total and subtract.

Next: working with abstract finite types whose cardinality comes from
a hypothesis.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
