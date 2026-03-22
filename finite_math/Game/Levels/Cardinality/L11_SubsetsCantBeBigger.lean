import Game.Metadata

World "Cardinality"
Level 11

Title "Subsets Can't Be Bigger"

Introduction "
# Monotonicity of Cardinality

If every element of `s` is also in `t`, then `s` can't have more
elements than `t`:

$$s \\subseteq t \\implies |s| \\leq |t|$$

In Lean:
```
Finset.card_le_card : s ⊆ t → s.card ≤ t.card
```

This is **monotonicity**: cardinality respects the subset relation.
You can read it as: 'a part is never bigger than the whole.'

**Your task**: Given `s ⊆ t` and `t.card = 5`, prove that `s` has at
most 5 elements.
"

/-- A subset of a 5-element set has at most 5 elements. -/
Statement (s t : Finset ℕ) (h : s ⊆ t) (ht : t.card = 5) :
    s.card ≤ 5 := by
  Hint "Use `Finset.card_le_card h` to get `s.card ≤ t.card`, then
  combine with `ht` using `omega`."
  Hint (hidden := true) "Try `have hm := Finset.card_le_card h` and
  then `omega`."
  have hm := Finset.card_le_card h
  omega

Conclusion "
The `have` + `omega` pattern again:
1. `have hm := Finset.card_le_card h` — bring the cardinality bound
   into context
2. `omega` — combine `hm : s.card ≤ t.card` with `ht : t.card = 5`
   to conclude `s.card ≤ 5`

Monotonicity is surprisingly powerful. Combined with other card lemmas,
it lets you prove cardinality bounds without knowing the exact size.
For example, since `s.filter p ⊆ s`, you get
`(s.filter p).card ≤ s.card` — filtering never makes a set larger.

**Warning — the converse is false**: `|s| ≤ |t|` does NOT imply
`s ⊆ t`. For example, `|{1, 2}| = 2 ≤ 3 = |{3, 4, 5}|`, but
`{1, 2} ⊄ {3, 4, 5}` since `1 ∉ {3, 4, 5}`. Smaller cardinality
means fewer elements, not that every element belongs to the larger set.
"

/-- `Finset.card_le_card h` states that when `h : s ⊆ t`,
`s.card ≤ t.card`.

## Syntax
```
have hm := Finset.card_le_card h
```

## When to use it
When you have a subset relation `s ⊆ t` and need a cardinality
bound `s.card ≤ t.card`.

## The contrapositive
If `t.card < s.card`, then `s ⊄ t`. This is a useful reasoning
direction: more elements means there's something in `s` that's
not in `t`.
-/
TheoremDoc Finset.card_le_card as "Finset.card_le_card" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_le_card

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
