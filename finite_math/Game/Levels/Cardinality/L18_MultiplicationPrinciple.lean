import Game.Metadata

World "Cardinality"
Level 18

Title "The Multiplication Principle"

Introduction "
# Counting Pairs

If you can choose one item from $s$ and one from $t$, how many
combined choices do you have? The answer is $|s| \\times |t|$.

In Lean, `s ×ˢ t` is the **product** of two finsets — the set of
all pairs $(a, b)$ with $a \\in s$ and $b \\in t$:

$$|s \\times^s t| = |s| \\cdot |t|$$

```
Finset.card_product s t : (s ×ˢ t).card = s.card * t.card
```

This is the **multiplication principle** — the second most important
counting identity after inclusion-exclusion.

**Your task**: Given two finsets of known sizes, compute the size
of their product.
"

/-- Compute the product cardinality from the individual sizes. -/
Statement (s t : Finset ℕ) (hs : s.card = 4) (ht : t.card = 3) :
    (s ×ˢ t).card = 12 := by
  Hint "Apply `Finset.card_product` to rewrite the left side,
  then substitute the known sizes."
  Hint (hidden := true) "Try `rw [Finset.card_product, hs, ht]`.
  This rewrites the goal step by step:
  `(s ×ˢ t).card` → `s.card * t.card` → `4 * t.card` → `4 * 3`."
  rw [Finset.card_product, hs, ht]

Conclusion "
The multiplication principle: $|s \\times^s t| = |s| \\cdot |t|$.

Unlike the additive card lemmas (`have` + `omega`), the product lemma
involves multiplication, so we use `rw` instead:
`rw [Finset.card_product, hs, ht]` directly computes the result.

**Why 'product'?** The notation `s ×ˢ t` is the Cartesian product
specialized to finsets. Just as `Fin m × Fin n` has `m * n` elements
(which you could verify by exhaustive case analysis from Phase 1),
`s ×ˢ t` has `s.card * t.card` elements.

The multiplication principle combines with inclusion-exclusion:
- **Addition**: $|A \\cup B| = |A| + |B| - |A \\cap B|$ (for overlapping choices)
- **Multiplication**: $|A \\times B| = |A| \\cdot |B|$ (for independent choices)

Together they handle the two fundamental counting scenarios:
'choose from A or B' vs. 'choose from A and B.'
"

TheoremTab "Card"
NewTheorem Finset.card_product

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith
