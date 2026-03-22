import Game.Metadata

World "PsetCardinality"
Level 9

Title "Subtype Complement"

Introduction "
# Complement Counting with Equivalence

Given a type `α` equivalent to `Fin 5 × Bool` and a predicate `P`
with 3 elements satisfying it, how many elements satisfy `¬P`?

$$|\\{x : \\alpha \\mid \\neg P\\,x\\}| = |\\alpha| - |\\{x : \\alpha \\mid P\\,x\\}| = 10 - 3 = 7$$

This combines two Fintype skills:
- The **complement formula** for subtypes
- **Equivalence resolution** + product decomposition to compute $|\\alpha|$
"

/-- The complement subtype has 7 elements. -/
Statement (α : Type*) [Fintype α] [DecidableEq α]
    (e : α ≃ Fin 5 × Bool)
    (P : α → Prop) [DecidablePred P] [Fintype {x // P x}] [Fintype {x // ¬P x}]
    (hp : Fintype.card {x // P x} = 3) :
    Fintype.card {x // ¬P x} = 7 := by
  Hint "Two steps: first compute |α| in a `have` block, then apply the
  complement formula. Separate 'how big is the whole type?' from
  'how big is the complement?'"
  Hint (hidden := true) "You need: `card_congr`, `card_prod`, `card_fin`,
  `card_bool` (to compute |α|), then `card_subtype_compl` and `hp`."
  Hint (hidden := true) "Full proof — first compute |α| = 10:
  `have hα : Fintype.card α = 10 := by`
  `  rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]`
  then apply the complement formula:
  `rw [Fintype.card_subtype_compl, hα, hp]`"
  have hα : Fintype.card α = 10 := by
    Hint "Resolve α via the equivalence, then decompose the product."
    Hint (hidden := true) "Try `rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]`."
    rw [Fintype.card_congr e, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
  Hint "Good — `hα : Fintype.card α = 10`. Now apply the complement
  formula with `card_subtype_compl`, then substitute `hα` and `hp`."
  Hint (hidden := true) "Try `rw [Fintype.card_subtype_compl, hα, hp]`."
  rw [Fintype.card_subtype_compl, hα, hp]

Conclusion "
$$|\\{x : \\alpha \\mid \\neg P\\,x\\}| = |\\alpha| - |P| = 10 - 3 = 7$$

This time the proof had two phases:

| Phase | What | How |
|---|---|---|
| 1 | Compute $|\\alpha| = 10$ | `card_congr e`, `card_prod`, `card_fin`, `card_bool` |
| 2 | Apply complement formula | `card_subtype_compl`, substitute `hα` and `hp` |

The `have` block isolates the type-size computation from the
complement formula — structurally different from a flat rw chain.
When a proof has two distinct sub-tasks, separating them into
a `have` block makes the logic clearer.

This is the type-level version of complement counting from the
Cardinality world. Same mathematical idea, different formalism.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
