import Game.Metadata

World "Cardinality"
Level 4

Title "Positive Cardinality Means Nonempty"

Introduction "
# The Other Direction

In Level 3, you used `Finset.card_pos` to convert `s.Nonempty`
into `0 < s.card`. That was the **backward** direction of `card_pos`.

Now practice the **forward** direction: given that a finset has
positive cardinality, derive that it's nonempty.

`Finset.card_pos : 0 < s.card ↔ s.Nonempty`

When the goal is `s.Nonempty` and you know `0 < s.card`, you
can rewrite with `← Finset.card_pos` to convert the goal to
`0 < s.card`, or just use `rw [Finset.card_pos]` on the hypothesis.

**Your task**: Given that `s.card = 5`, prove `s.Nonempty`.
"

/-- A finset with 5 elements is nonempty. -/
Statement (s : Finset ℕ) (hs : s.card = 5) : s.Nonempty := by
  Hint "The goal is `s.Nonempty`. You can convert this to a
  cardinality condition using `← Finset.card_pos`:
  `rw [← Finset.card_pos]` changes the goal to `0 < s.card`."
  rw [← Finset.card_pos]
  Hint "The goal is now `0 < s.card`. Use `hs` to substitute
  the known cardinality, then `omega` closes the goal."
  Hint (hidden := true) "`rw [hs]` or just `omega`."
  omega

Conclusion "
You've now used `card_pos` in both directions:

| Direction | Pattern | What it does |
|---|---|---|
| Forward (L3) | `rw [Finset.card_pos]` | Convert `0 < s.card` to `s.Nonempty` |
| Backward (this) | `rw [← Finset.card_pos]` | Convert `s.Nonempty` to `0 < s.card` |

This bidirectional bridge between the qualitative (`Nonempty`) and
quantitative (`card > 0`) views is a recurring pattern. Whenever you
know a cardinality fact and need an existence fact, or vice versa,
`card_pos` is the tool.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
