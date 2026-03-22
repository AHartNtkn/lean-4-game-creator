import Game.Metadata

World "Fintype"
Level 7

Title "Mixing Types"

Introduction "
# Practice: Combining card_* Lemmas

You've learned three composition rules:

| Principle | Lemma | Formula |
|---|---|---|
| Multiplication | `card_prod` | `card (α × β) = card α * card β` |
| Addition | `card_sum` | `card (α ⊕ β) = card α + card β` |
| Exponentiation | `card_fun` | `card (α → β) = card β ^ card α` |

These work for ANY finite types — not just `Fin n`. You can mix `Fin`,
`Bool`, and composite types freely.

**Your task**: Compute the cardinality of `Bool × Fin n`. Use
`card_prod` followed by `card_bool` and `card_fin`.
"

/-- Bool × Fin n has 2 * n elements. -/
Statement (n : ℕ) : Fintype.card (Bool × Fin n) = 2 * n := by
  Hint "Start with `rw [Fintype.card_prod]` to split into
  `Fintype.card Bool * Fintype.card (Fin n)`."
  rw [Fintype.card_prod]
  Hint "Now rewrite each factor: `rw [Fintype.card_bool, Fintype.card_fin]`."
  rw [Fintype.card_bool, Fintype.card_fin]

Conclusion "
You combined `card_prod` with `card_bool` — the first time a
composition rule was used with a non-`Fin` factor.

For example, the 6 elements of `Bool × Fin 3` are:
`(false, 0), (false, 1), (false, 2), (true, 0), (true, 1), (true, 2)`

The card_* lemmas compose freely. Any expression built from finite
types using `×`, `⊕`, and `→` has a computable cardinality.

Next: there's one more composition rule — subtypes.
"

TheoremTab "Fintype"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
