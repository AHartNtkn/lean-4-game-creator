import Game.Metadata

World "Products"
Level 5

Title "Product Cardinality Integration"

Introduction "
# Combining Product and Union Cardinalities

You know `card_product` from the Cardinality world. Let's combine
it with other cardinality lemmas.

If `s` has 3 elements and `t₁` and `t₂` are disjoint with
`t₁.card = 2` and `t₂.card = 4`, how many pairs are in
`s ×ˢ (t₁ ∪ t₂)`?

**Strategy**: Rewrite `card_product`, then `card_union_of_disjoint`,
then substitute the known sizes.
"

/-- Combine product and union cardinality. -/
Statement (s : Finset ℕ) (t₁ t₂ : Finset ℕ)
    (hs : s.card = 3) (ht₁ : t₁.card = 2) (ht₂ : t₂.card = 4)
    (hdisj : Disjoint t₁ t₂) :
    (s ×ˢ (t₁ ∪ t₂)).card = 18 := by
  Hint "Start with `rw [Finset.card_product]` to split the
  product cardinality into `s.card * (t₁ ∪ t₂).card`."
  rw [Finset.card_product]
  Hint "Now handle the union cardinality. Since `t₁` and `t₂`
  are disjoint, use `Finset.card_union_of_disjoint`."
  Hint (hidden := true) "Try `rw [Finset.card_union_of_disjoint hdisj]`."
  rw [Finset.card_union_of_disjoint hdisj]
  Hint "Substitute the known sizes."
  Hint (hidden := true) "Try `rw [hs, ht₁, ht₂]`."
  rw [hs, ht₁, ht₂]

Conclusion "
This level combines two cardinality tools:

- `card_product`: $|s \\times^s t| = |s| \\cdot |t|$
- `card_union_of_disjoint`: $|t_1 \\cup t_2| = |t_1| + |t_2|$ when disjoint

The result: $3 \\times (2 + 4) = 18$.

Integration like this is the point of having a toolkit — individual
lemmas combine to solve problems that no single lemma handles.

**Observations worth noting**: Since `card_product` gives
$|s \\times^s t| = |s| \\cdot |t|$, commutativity of multiplication
immediately tells us $(s \\times^s t).\\text{card} = (t \\times^s s).\\text{card}$
— swapping the factors doesn't change the count. At the
boundary: $(\\emptyset \\times^s t).\\text{card} = 0$ (the empty product
is empty) and $(\\{a\\} \\times^s t).\\text{card} = t.\\text{card}$ (the
product with a singleton is a copy of the other set). These
edge cases confirm that `card_product` behaves as expected.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
