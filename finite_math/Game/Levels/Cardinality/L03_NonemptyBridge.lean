import Game.Metadata

World "Cardinality"
Level 3

Title "Nonempty Means Positive Cardinality"

Introduction "
# Bridging Qualitative and Quantitative

In FinsetBasics, you learned `Finset.Nonempty s` — a qualitative
property meaning 'there exists some element in `s`.' Now you have
`s.card` — a quantitative measure of how many elements `s` contains.

How do these connect? A finset is nonempty if and only if its
cardinality is positive:

$$s.\\text{Nonempty} \\leftrightarrow 0 < |s|$$

In Lean: `Finset.card_pos : 0 < s.card ↔ s.Nonempty`

This bridges the qualitative and quantitative views:
- If you know `s` contains some element, then `|s| ≥ 1`
- If you know `|s| > 0`, then there must be some element in `s`

**Your task**: Given that `s` is nonempty and has cardinality 3,
prove that `0 < s.card`. Use the backward direction of `card_pos`.
"

/-- Nonempty finsets have positive cardinality. -/
Statement (s : Finset ℕ) (hs : s.Nonempty) : 0 < s.card := by
  Hint "The goal `0 < s.card` matches the LEFT side of
  `Finset.card_pos`. Use `rw [Finset.card_pos]` to convert
  the goal to `s.Nonempty`."
  rw [Finset.card_pos]
  Hint "The goal is now `s.Nonempty`, which is exactly `hs`."
  Hint (hidden := true) "Try `exact hs`."
  exact hs

Conclusion "
`Finset.card_pos` connects two ways of saying 'the set isn't empty':
- **Qualitative**: `s.Nonempty` (there exists an element)
- **Quantitative**: `0 < s.card` (the count is positive)

The equivalence is `0 < s.card ↔ s.Nonempty`. You used `rw` to
convert between the two forms — a pattern you'll see whenever
you need to switch between the existential and counting perspectives.

The contrapositive is equally useful: `s.card = 0 ↔ s = ∅`. If the
cardinality is zero, the set must be empty — and vice versa.
"

/-- `Finset.card_pos` states `0 < s.card ↔ s.Nonempty`.

## Syntax
```
rw [Finset.card_pos]
```

## When to use it
When you need to convert between `0 < s.card` (quantitative) and
`s.Nonempty` (qualitative). Both directions are useful:
- `rw [Finset.card_pos]`: convert `0 < s.card` to `s.Nonempty`
- `rw [← Finset.card_pos]`: convert `s.Nonempty` to `0 < s.card`
-/
TheoremDoc Finset.card_pos as "Finset.card_pos" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_pos

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
