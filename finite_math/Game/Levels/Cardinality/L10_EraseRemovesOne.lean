import Game.Metadata

World "Cardinality"
Level 10

Title "Erase Removes One"

Introduction "
# Removing an Element

`insert` adds one element and increases the count by 1. The dual
operation is `Finset.erase`: remove one element, and the count
decreases by 1.

$$a \\in s \\implies |s.\\text{erase}\\;a| = |s| - 1$$

In Lean:
```
Finset.card_erase_of_mem : a ∈ s → (s.erase a).card = s.card - 1
```

The hypothesis `a ∈ s` is required — if `a ∉ s`, then erasing it
does nothing.

Note the subtraction is on natural numbers. Since `.card` returns a
`ℕ`, we use natural number subtraction (which floors at 0). When
`a ∈ s`, we know `s.card ≥ 1`, so `s.card - 1` behaves as expected.

**Your task**: Given `a ∈ s` and `s.card = 5`, prove that erasing `a`
leaves 4 elements.
"

/-- Erasing a member from a 5-element set leaves 4 elements. -/
Statement (s : Finset ℕ) (a : ℕ) (h : a ∈ s) (hs : s.card = 5) :
    (s.erase a).card = 4 := by
  Hint "First, use `Finset.card_erase_of_mem h` to get the general
  equation: `(s.erase a).card = s.card - 1`."
  Hint (hidden := true) "Try `have he := Finset.card_erase_of_mem h`
  to add the equation to your context. Then use `omega` to combine
  it with `hs`."
  have he := Finset.card_erase_of_mem h
  Hint "Now you have `he : (s.erase a).card = s.card - 1` and
  `hs : s.card = 5`. The arithmetic `5 - 1 = 4` is handled by `omega`."
  omega

Conclusion "
The `have` + `omega` pattern is powerful for cardinality reasoning:
1. Use `have` to bring a card lemma into the context
2. Use `omega` to handle the arithmetic

This is better than trying to `rw` card lemmas directly into the
goal, because `omega` can combine multiple arithmetic facts at once.
You'll use this pattern repeatedly in the remaining levels.

`card_erase_of_mem` is the complement of `card_insert_of_notMem`:
- Insert a new element: size goes up by 1
- Erase an existing element: size goes down by 1
"

/-- `Finset.card_erase_of_mem h` states that when `h : a ∈ s`,
`(s.erase a).card = s.card - 1`.

## Syntax
```
have he := Finset.card_erase_of_mem h
```

## When to use it
When you need to relate the cardinality of `s.erase a` to `s.card`,
knowing that `a ∈ s`.

## Warning
The subtraction is over `ℕ`, so `s.card - 1` is natural number
subtraction (which floors at 0). When `a ∈ s`, we know `s.card ≥ 1`,
so this subtraction is exact.
-/
TheoremDoc Finset.card_erase_of_mem as "Finset.card_erase_of_mem" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_erase_of_mem

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
