import Game.Metadata

World "AbstractionLadder"
Level 4

Title "Appending Lists"

Introduction "
# List Append and Length

Lists can be joined with `++` (append):

`[1, 2] ++ [3, 4] = [1, 2, 3, 4]`

The key length fact for append is:

`List.length_append : (l₁ ++ l₂).length = l₁.length + l₂.length`

This is the list-level version of the addition principle: the length
of a concatenation is the sum of the lengths.

**Your task**: Given two lists with known lengths, determine the length
of their concatenation.
"

/-- The length of a concatenation equals the sum of the lengths. -/
Statement (l₁ l₂ : List ℕ) (h₁ : l₁.length = 3) (h₂ : l₂.length = 4) :
    (l₁ ++ l₂).length = 7 := by
  Hint "Start by rewriting with `List.length_append` to split the
  concatenation length into a sum."
  rw [List.length_append]
  Hint "Now the goal is `l₁.length + l₂.length = 7`. Rewrite with
  the hypotheses `h₁` and `h₂`."
  rw [h₁, h₂]

Conclusion "
`List.length_append` is the additive decomposition for list length.
Combined with `length_cons` and `length_nil`, you can compute the
length of any list expression.

In plain math: $|l_1 \\cdot l_2| = |l_1| + |l_2|$ where $\\cdot$ is
concatenation.

**Why this matters for the ladder**: When we quotient lists to get
multisets, this length fact becomes `Multiset.card_add`. The
arithmetic is preserved even though the ordering is forgotten.
"

/-- `List.length_append` states that
`(l₁ ++ l₂).length = l₁.length + l₂.length`.

## Syntax
```
rw [List.length_append]
```

## When to use it
When the goal involves the length of an appended list `(l₁ ++ l₂).length`.
-/
TheoremDoc List.length_append as "List.length_append" in "List"

TheoremTab "List"
NewTheorem List.length_append

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
