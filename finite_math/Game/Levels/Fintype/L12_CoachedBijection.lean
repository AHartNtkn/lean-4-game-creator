import Game.Metadata

World "Fintype"
Level 12

Title "Bijection + Composition"

Introduction "
# Chaining card_congr with card_*

The real power of `Fintype.card_congr` appears when the target type
is itself composite. Given `e : α ≃ Fin 2 × Fin 3`, you can:

1. Use `card_congr e` to reduce `card α` to `card (Fin 2 × Fin 3)`
2. Use `card_prod` to split into `card (Fin 2) * card (Fin 3)`
3. Use `card_fin` to evaluate each factor

This chains three lemmas: equivalence transfer, then decomposition,
then evaluation.

**Your task**: Given `e : α ≃ Fin 2 × Fin 3`, prove that `α` has
6 elements.
"

/-- If α is equivalent to Fin 2 × Fin 3, then α has 6 elements. -/
Statement (α : Type*) [Fintype α] (e : α ≃ Fin 2 × Fin 3) :
    Fintype.card α = 6 := by
  Hint "Chain three rewrites: first `Fintype.card_congr e` to transfer
  across the equivalence, then `Fintype.card_prod` to decompose,
  then `Fintype.card_fin` to evaluate."
  Hint (hidden := true) "Try `rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

Conclusion "
You chained three tools:

| Step | Lemma | Effect |
|---|---|---|
| 1 | `card_congr e` | `card α → card (Fin 2 × Fin 3)` |
| 2 | `card_prod` | `→ card (Fin 2) * card (Fin 3)` |
| 3 | `card_fin` (×2) | `→ 2 * 3 = 6` |

This is the bijective counting workflow: **transfer, decompose, evaluate**.

In practice, you'd use this when `α` is some combinatorial object
(permutations, partitions, colorings) and you prove it's equivalent to
a known product/sum type to determine its size.

Next: practice the final step — closing arithmetic goals with `omega`.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
