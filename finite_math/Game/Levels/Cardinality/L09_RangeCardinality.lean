import Game.Metadata

World "Cardinality"
Level 9

Title "Comparing Range Sizes"

Introduction "
# Cardinality of Range

You learned `Finset.card_range` in the Finset Problem Set:

$$|\\text{range}(n)| = n$$

In Lean: `Finset.card_range n : (Finset.range n).card = n`

This level puts it to work: use `card_range` to determine two
range sizes, then let the arithmetic resolve the comparison.

**Your task**: Prove that `range 10` has 3 more elements than `range 7`.
"

/-- range 10 has 3 more elements than range 7. -/
Statement : (Finset.range 10).card = (Finset.range 7).card + 3 := by
  Hint "Apply `Finset.card_range` to both sides. You can chain two
  rewrites: `rw [Finset.card_range, Finset.card_range]`."
  Hint (hidden := true) "Try `rw [Finset.card_range, Finset.card_range]`.
  After both rewrites the goal reduces to `10 = 7 + 3`, which Lean
  closes automatically."
  rw [Finset.card_range, Finset.card_range]

Conclusion "
`Finset.card_range n` turns abstract range cardinalities into concrete
numbers. Once both sides are numerical, Lean's kernel reduction handles
the arithmetic.

You first met `card_range` in PsetFinset Level 9. It will continue to
appear whenever finset cardinality meets natural number indexing.

**Coming up**: The next level introduces the `have` + `omega` pattern
— bringing a card lemma into context with `have`, then using `omega`
for the arithmetic. This is the main proof strategy for the rest of
the world.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
