import Game.Metadata

World "Products"
Level 15

Title "Off-Diagonal Cardinality"

Introduction "
# Counting Distinct Pairs

The off-diagonal contains all ordered pairs of *distinct* elements
from `s`. Its cardinality is:

$$|s.\\text{offDiag}| = |s|^2 - |s|$$

In Lean:
```
Finset.offDiag_card : (Finset.offDiag s).card = s.card * s.card - s.card
```

This makes sense: `s ×ˢ s` has $|s|^2$ pairs total, and `s.diag`
accounts for $|s|$ of them (the self-pairs). Removing the diagonal
leaves $|s|^2 - |s|$ distinct pairs.

**Your task**: Given `s.card = 4`, compute `s.offDiag.card`.
"

/-- The off-diagonal has card^2 - card elements. -/
Statement (s : Finset ℕ) (hs : s.card = 4) :
    s.offDiag.card = 12 := by
  Hint "Apply `Finset.offDiag_card` to express the off-diagonal
  cardinality in terms of `s.card`."
  Hint (hidden := true) "Try `rw [Finset.offDiag_card]`."
  rw [Finset.offDiag_card]
  Hint "Now substitute `s.card = 4` and compute."
  Hint (hidden := true) "Try `rw [hs]`."
  rw [hs]

Conclusion "
$|s.\\text{offDiag}| = 4 \\times 4 - 4 = 16 - 4 = 12$.

These 12 pairs are the **ordered** pairs of distinct elements
from a 4-element set. In combinatorics notation, this is the
number of **2-permutations** of 4 elements:

$$P(4, 2) = 4 \\times 3 = 12$$

Note that `offDiag_card` writes the formula as $|s|^2 - |s|$
rather than $|s| \\cdot (|s| - 1)$ — they're equal, but the
squared form avoids natural number subtraction issues.
"

/-- `Finset.offDiag_card` states that

`(Finset.offDiag s).card = s.card * s.card - s.card`

The off-diagonal has `card^2 - card` elements: the total number
of pairs minus the diagonal pairs.

## Syntax
```
rw [Finset.offDiag_card]
```

## When to use it
When the goal involves `s.offDiag.card`.

## Note
The formula uses `s.card * s.card - s.card` rather than
`s.card * (s.card - 1)`. Both are mathematically equal, but
the squared form avoids Nat subtraction edge cases.
-/
TheoremDoc Finset.offDiag_card as "Finset.offDiag_card" in "Product"

TheoremTab "Product"
NewTheorem Finset.offDiag_card

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
