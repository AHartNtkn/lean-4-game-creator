import Game.Metadata

World "Finale"
Level 3

Title "Diagonal Decomposition"

Introduction "
# Counting Pairs by Decomposition

The self-product $s \\times^s s$ contains all ordered pairs from $s$.
These pairs split into two groups:

- **Diagonal** $s.\\text{diag}$: pairs $(a, a)$ where both components
  are the same element
- **Off-diagonal** $s.\\text{offDiag}$: pairs $(a, b)$ where $a \\ne b$

From the Products world, you know:
- `Finset.diag_union_offDiag s` : $s.\\text{diag} \\cup s.\\text{offDiag} = s \\times^s s$
- `Finset.disjoint_diag_offDiag s` : the two groups are disjoint
- `Finset.diag_card s` : $|s.\\text{diag}| = |s|$

Combine these with `card_union_of_disjoint` and `card_product`
to prove the decomposition identity.
"

/-- The off-diagonal count plus the diagonal count equals n². -/
Statement (s : Finset ℕ) :
    s.offDiag.card + s.card = s.card * s.card := by
  Hint "Start by establishing the decomposition of `s ×ˢ s` into
  diagonal and off-diagonal parts."
  Hint (hidden := true) "Try
  `have h_card := Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)`."
  have h_card := Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)
  Hint "Now `h_card` says `(diag ∪ offDiag).card = diag.card + offDiag.card`.
  Rewrite the left side using `diag_union_offDiag` to get `(s ×ˢ s).card`."
  Hint (hidden := true) "Try `rw [Finset.diag_union_offDiag] at h_card`."
  rw [Finset.diag_union_offDiag] at h_card
  Hint "Compute `s.diag.card` using `Finset.diag_card`."
  Hint (hidden := true) "Try `rw [Finset.diag_card] at h_card`."
  rw [Finset.diag_card] at h_card
  Hint "Now bring in the product cardinality: `(s ×ˢ s).card = s.card * s.card`."
  Hint (hidden := true) "Try `have h_prod := Finset.card_product s s`."
  have h_prod := Finset.card_product s s
  Hint "Now `h_card` says `(s ×ˢ s).card = s.card + s.offDiag.card` and
  `h_prod` says `(s ×ˢ s).card = s.card * s.card`. Combine with `omega`."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
**The decomposition chain**:

| Step | Tool | Result |
|------|------|--------|
| 1 | `disjoint_diag_offDiag` + `card_union_of_disjoint` | $|\\text{diag} \\cup \\text{offDiag}| = |\\text{diag}| + |\\text{offDiag}|$ |
| 2 | `diag_union_offDiag` | LHS becomes $|s \\times^s s|$ |
| 3 | `diag_card` | $|\\text{diag}| = |s|$ |
| 4 | `card_product` | $|s \\times^s s| = n^2$ |
| 5 | `omega` | close the arithmetic |

This is the **partition-then-count** strategy: decompose a set
into disjoint parts, count each part separately, then combine.
It's the same strategy behind inclusion-exclusion and fiber
decomposition — different decompositions, same pattern.

**The closed form you derived**: $|\\text{offDiag}| + n = n^2$,
so $|\\text{offDiag}| = n^2 - n = n(n-1)$.
The $n(n-1)$ ordered pairs with distinct components are the
building blocks for counting permutations.

**Connection to binomial coefficients**: Since
$n(n-1) = 2 \\cdot \\binom{n}{2}$, the off-diagonal count is
exactly twice the number of 2-element subsets. The factor of 2
reflects the difference between **ordered** and **unordered**
pairs: $s.\\text{offDiag}$ counts both $(a,b)$ and $(b,a)$,
while $\\binom{n}{2}$ counts each unordered pair once.
"

/-- `Finset.offDiag_card` computes the number of off-diagonal pairs:
`s.offDiag.card = s.card * (s.card - 1)`.

Disabled here so you derive the relationship from the decomposition.
-/
TheoremDoc Finset.offDiag_card as "Finset.offDiag_card" in "Product"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith nlinarith
DisabledTheorem Finset.offDiag_card
