import Game.Metadata

World "Cardinality"
Level 20

Title "Everything Lives in Univ"

Introduction "
# Bounding Cardinality via Univ

Every finset of a finite type is a subset of `Finset.univ`:

```
Finset.subset_univ s : s ⊆ Finset.univ
```

This is the finset version of 'every element belongs to the universe.'

Combined with `card_le_card` (subsets have smaller cardinality), this
gives an upper bound on any finset's size:

$$|s| \\leq |\\text{Fin}\\;n| = n$$

The proof pattern:
1. `Finset.subset_univ s` gives `s ⊆ Finset.univ`
2. `Finset.card_le_card` converts subset to `s.card ≤ Finset.univ.card`
3. `Finset.card_univ` + `Fintype.card_fin` evaluates `Finset.univ.card`

**Your task**: Prove that any finset of `Fin 4` elements has at most
4 elements.
"

/-- Any finset of Fin 4 has at most 4 elements. -/
Statement (s : Finset (Fin 4)) : s.card ≤ 4 := by
  Hint "Use `Finset.subset_univ s` to get the subset relation,
  then `Finset.card_le_card` to convert it to a cardinality bound."
  Hint (hidden := true) "Try:
  `have h1 := Finset.card_le_card (Finset.subset_univ s)`
  `rw [Finset.card_univ, Fintype.card_fin] at h1`
  `exact h1`"
  have h1 := Finset.card_le_card (Finset.subset_univ s)
  Hint "Now `h1 : s.card ≤ Finset.univ.card`. Simplify the right side
  using `card_univ` and `card_fin`."
  rw [Finset.card_univ, Fintype.card_fin] at h1
  Hint "Now `h1 : s.card ≤ 4`. This is exactly the goal."
  exact h1

Conclusion "
You composed three tools:
1. `subset_univ` — every finset is a subset of the universe
2. `card_le_card` — subsets have smaller cardinality
3. `card_univ` + `card_fin` — the universe has `n` elements

This gives the fundamental upper bound: no finset of `Fin n` elements
can have more than `n` elements. This may seem obvious, but it's the
key ingredient for the next level: proving the pigeonhole principle
via cardinality.
"

/-- `Finset.subset_univ s` states that every finset `s` is a subset of `Finset.univ`.

This is the finset version of 'every element belongs to the universe.'
-/
TheoremDoc Finset.subset_univ as "Finset.subset_univ" in "Finset"

NewTheorem Finset.subset_univ

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
DisabledTheorem Finset.card_le_univ Finset.eq_univ_of_card
