import Game.Metadata

World "Products"
Level 14

Title "Diagonal Cardinality"

Introduction "
# How Big Is the Diagonal?

Since `s.diag` has one pair `(a, a)` for each `a ∈ s`, its
cardinality equals `s.card`:

```
Finset.diag_card : (Finset.diag s).card = s.card
```

**Your task**: Given `s.card = 5`, compute `s.diag.card`.
"

/-- The diagonal has the same cardinality as the original set. -/
Statement (s : Finset ℕ) (hs : s.card = 5) :
    s.diag.card = 5 := by
  Hint "Rewrite with `Finset.diag_card` to replace
  `s.diag.card` with `s.card`."
  Hint (hidden := true) "Try `rw [Finset.diag_card]`."
  rw [Finset.diag_card]
  Hint "Now the goal is `s.card = 5`, which is your hypothesis."
  exact hs

Conclusion "
One pair per element: $|s.\\text{diag}| = |s|$.

This makes intuitive sense — the diagonal is a 'copy' of `s`
inside the product `s ×ˢ s`, with each element mapped to its
self-pair.
"

/-- `Finset.diag_card` states that the diagonal has the same
cardinality as the original finset:

`(Finset.diag s).card = s.card`

## Syntax
```
rw [Finset.diag_card]
```

## When to use it
When the goal involves `s.diag.card` or `(Finset.diag s).card`.
-/
TheoremDoc Finset.diag_card as "Finset.diag_card" in "Product"

TheoremTab "Product"
NewTheorem Finset.diag_card

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith
