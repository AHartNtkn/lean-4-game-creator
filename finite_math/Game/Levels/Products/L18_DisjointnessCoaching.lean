import Game.Metadata

World "Products"
Level 18

Title "Disjointness and Cardinality"

Introduction "
# The Diagonal and Off-Diagonal Are Disjoint

The previous level showed that `s ×ˢ s = s.diag ∪ s.offDiag`.
For this decomposition to be useful for **counting**, we need
to know the union is **disjoint** — no pair belongs to both
the diagonal and the off-diagonal.

This is `Finset.disjoint_diag_offDiag`:

```
Finset.disjoint_diag_offDiag : Disjoint s.diag s.offDiag
```

A pair `(a, b)` in the diagonal has `a = b`. A pair in the
off-diagonal has `a ≠ b`. These conditions are contradictory,
so the intersection is empty.

**Combined with `card_union_of_disjoint`**: When two finsets
are disjoint, the cardinality of their union is the sum:

$$|A \\cup B| = |A| + |B| \\quad \\text{when } A \\cap B = \\emptyset$$

**Your task**: Given `s.card = 3`, compute
`(s.diag ∪ s.offDiag).card`.
"

/-- Compute the cardinality of a disjoint diagonal/off-diagonal union. -/
Statement (s : Finset ℕ) (hs : s.card = 3) :
    (s.diag ∪ s.offDiag).card = 9 := by
  Hint "The diagonal and off-diagonal are disjoint. Use
  `Finset.card_union_of_disjoint` with `Finset.disjoint_diag_offDiag`
  to split the union cardinality into a sum."
  Hint (hidden := true) "Try
  `rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]`.

  `Finset.disjoint_diag_offDiag s` provides the disjointness proof,
  and `card_union_of_disjoint` converts the union cardinality to a sum."
  rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]
  Hint "Now compute `s.diag.card` using `Finset.diag_card`."
  Hint (hidden := true) "Try `rw [Finset.diag_card]`."
  rw [Finset.diag_card]
  Hint "And `s.offDiag.card` using `Finset.offDiag_card`."
  Hint (hidden := true) "Try `rw [Finset.offDiag_card]`."
  rw [Finset.offDiag_card]
  Hint "Substitute `s.card = 3` to finish."
  Hint (hidden := true) "Try `rw [hs]`.
  This gives `3 + (3 * 3 - 3) = 3 + 6 = 9`."
  rw [hs]

Conclusion "
The computation breaks down as:

$$|s.\\text{diag} \\cup s.\\text{offDiag}| = |s.\\text{diag}| + |s.\\text{offDiag}|
= 3 + (9 - 3) = 3 + 6 = 9 = 3^2$$

No surprise — `s.diag ∪ s.offDiag = s ×ˢ s` and
`(s ×ˢ s).card = s.card * s.card = 9`.

But the **decomposition route** reveals *why* $n^2 = n + n(n-1)$:
the $n$ pairs on the diagonal plus the $n(n-1)$ pairs off the
diagonal account for all $n^2$ pairs in `s ×ˢ s`.

You now have all the tools for the boss level.
"

/-- `Finset.disjoint_diag_offDiag` states that

`Disjoint s.diag s.offDiag`

The diagonal and off-diagonal are disjoint: no pair is both
`(a, a)` and has `a ≠ b`.

## Syntax
```
Finset.disjoint_diag_offDiag s
Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)
```

## When to use it
When you need the disjointness of `s.diag` and `s.offDiag`,
typically to apply `card_union_of_disjoint`.
-/
TheoremDoc Finset.disjoint_diag_offDiag as "Finset.disjoint_diag_offDiag" in "Product"

TheoremTab "Product"
NewTheorem Finset.disjoint_diag_offDiag

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
