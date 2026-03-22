import Game.Metadata

World "Cardinality"
Level 5

Title "Zero Cardinality Means Empty"

Introduction "
# The Dual of card_pos

In Levels 3-4, you proved the `card_pos` bridge: positive
cardinality is equivalent to nonemptiness. Now prove the
**dual**: zero cardinality means the set is empty.

`Finset.card_eq_zero : s.card = 0 ↔ s = ∅`

This completes the picture:
- `card_pos`: $|s| > 0 \\iff s \\neq \\emptyset$
- `card_eq_zero`: $|s| = 0 \\iff s = \\emptyset$

Together they say: a finset is either empty (card 0) or nonempty
(card positive). There's no third option.

**Your task**: Given that `s.card = 0`, prove that `s = ∅`.
"

/-- A finset with zero elements is empty. -/
Statement (s : Finset ℕ) (hs : s.card = 0) : s = ∅ := by
  Hint "The theorem `Finset.card_eq_zero` gives the biconditional
  `s.card = 0 ↔ s = ∅`. You can use the forward direction:
  `exact Finset.card_eq_zero.mp hs`."
  Hint (hidden := true) "Or use `rw [← Finset.card_eq_zero]` to
  convert the goal to `s.card = 0`, then `exact hs`."
  exact Finset.card_eq_zero.mp hs

Conclusion "
You've completed the card_pos / card_eq_zero duality:

| Cardinality | Set is... | Theorem |
|---|---|---|
| $|s| = 0$ | empty ($s = \\emptyset$) | `Finset.card_eq_zero` |
| $|s| > 0$ | nonempty ($s.\\text{Nonempty}$) | `Finset.card_pos` |

In practice, `card_eq_zero` is one of the most-used cardinality
lemmas: whenever you know a set has zero elements, you can conclude
it's empty, which simplifies many proofs.
"

/-- `Finset.card_eq_zero` states that `s.card = 0 ↔ s = ∅`.

A finset has zero elements if and only if it is the empty set.

## Syntax
```
exact Finset.card_eq_zero.mp hs  -- from s.card = 0 to s = ∅
rw [← Finset.card_eq_zero]      -- convert goal s = ∅ to s.card = 0
```

## When to use it
When you know `s.card = 0` and need `s = ∅`, or vice versa.
-/
TheoremDoc Finset.card_eq_zero as "Finset.card_eq_zero" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_eq_zero

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
