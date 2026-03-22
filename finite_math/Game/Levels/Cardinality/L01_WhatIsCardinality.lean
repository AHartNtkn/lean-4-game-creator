import Game.Metadata

World "Cardinality"
Level 1

Title "What Is Cardinality?"

Introduction "
# Counting Elements: Finset.card

You've been working with finsets — building them, testing membership,
taking unions and intersections, computing images. But you haven't yet
asked the most basic counting question: **how many elements does a
finset contain?**

The answer is `Finset.card` (or `.card` in dot notation). For any
finset `s`, the expression `s.card` is a natural number giving the
number of elements in `s`.

The simplest fact: the empty finset has zero elements.

$$|\\emptyset| = 0$$

In Lean: `Finset.card_empty : (∅ : Finset α).card = 0`

**Your task**: Prove that the empty finset of natural numbers has
cardinality zero.
"

/-- The empty finset has zero elements. -/
Statement : (∅ : Finset ℕ).card = 0 := by
  Hint "The goal is `(∅ : Finset ℕ).card = 0`. This is exactly
  what `Finset.card_empty` says."
  Hint (hidden := true) "Try `exact Finset.card_empty`."
  exact Finset.card_empty

Conclusion "
`Finset.card_empty` is the base case for cardinality: the empty set
has zero elements. This is the starting point for building up
cardinality of larger sets — just as `∅` was the starting point for
building finsets by `insert`.

In plain math: $|\\emptyset| = 0$. This is the definition that makes
inductive cardinality arguments work.
"

/-- `Finset.card_empty` states that `(∅ : Finset α).card = 0`.

## Syntax
```
exact Finset.card_empty
rw [Finset.card_empty]
```

## When to use it
When the goal or a hypothesis involves the cardinality of the empty
finset.
-/
TheoremDoc Finset.card_empty as "Finset.card_empty" in "Card"

TheoremTab "Card"
NewTheorem Finset.card_empty

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
