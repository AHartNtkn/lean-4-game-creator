import Game.Metadata

World "Products"
Level 19

Title "The General Decomposition Identity"

Introduction "
# The Partition Identity for Self-Products

You've computed `(s.diag ∪ s.offDiag).card` for a specific value
of `s.card`. Now let's prove the **general identity** — without
assuming anything about `s.card`:

$$(s \\times^s s).\\text{card} = s.\\text{diag}.\\text{card} + s.\\text{offDiag}.\\text{card}$$

This says: the total number of pairs from `s` decomposes as
diagonal pairs plus off-diagonal pairs, for **any** finset `s`.

**Strategy**: Decompose `s ×ˢ s` using `← diag_union_offDiag`,
then apply `card_union_of_disjoint` with the disjointness proof.
"

/-- The self-product cardinality decomposes as diagonal plus off-diagonal. -/
Statement (s : Finset ℕ) :
    (s ×ˢ s).card = s.diag.card + s.offDiag.card := by
  Hint "Decompose `s ×ˢ s` into `s.diag ∪ s.offDiag` using the
  reverse rewrite."
  Hint (hidden := true) "Try `rw [← Finset.diag_union_offDiag]`."
  rw [← Finset.diag_union_offDiag]
  Hint "The union is disjoint — apply `card_union_of_disjoint`
  with `disjoint_diag_offDiag`."
  Hint (hidden := true) "Try
  `rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]`."
  rw [Finset.card_union_of_disjoint (Finset.disjoint_diag_offDiag s)]

Conclusion "
You've proved the **general decomposition identity**:

$$(s \\times^s s).\\text{card} = s.\\text{diag}.\\text{card} + s.\\text{offDiag}.\\text{card}$$

This holds for any finset `s` — no specific cardinality assumed.

**The partition-then-count pattern**:
1. Recognize that `s ×ˢ s` splits into two disjoint pieces
2. Apply `card_union_of_disjoint` to convert the union
   cardinality into a sum

This is the abstract skeleton. In the next level, you'll
substitute `diag_card` and `offDiag_card` to derive the
full algebraic identity, and then the boss will instantiate
it with a specific value of `s.card`.
"

TheoremTab "Product"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith ring ring_nf
