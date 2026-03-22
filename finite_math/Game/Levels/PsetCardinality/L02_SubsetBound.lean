import Game.Metadata

World "PsetCardinality"
Level 2

Title "Subset Bound"

Introduction "
# Bounding a Subset of a Union

You know $|s| = 6$, $|t| = 9$, and $|s \\cap t| = 2$. A finset
$u$ is a subset of $s \\cup t$.

**Your task**: Prove that $|u| \\leq 13$.

Think about what tools you need:
- **Inclusion-exclusion** gives you $|s \\cup t|$ from the known sizes
- **Monotonicity** turns a subset relationship into a cardinality bound
- **omega** combines the arithmetic
"

/-- A subset of a union has cardinality bounded by inclusion-exclusion. -/
Statement (s t u : Finset ℕ) (hu : u ⊆ s ∪ t)
    (hs : s.card = 6) (ht : t.card = 9) (hi : (s ∩ t).card = 2) :
    u.card ≤ 13 := by
  Hint "Start by computing |(s ∪ t)| with inclusion-exclusion."
  Hint (hidden := true) "Try `have h1 := Finset.card_union_add_card_inter s t`."
  have h1 := Finset.card_union_add_card_inter s t
  Hint "Good. Now bound |u| using monotonicity: since `u ⊆ s ∪ t`,
  we have `u.card ≤ (s ∪ t).card`."
  Hint (hidden := true) "Try `have h2 := Finset.card_le_card hu`."
  have h2 := Finset.card_le_card hu
  Hint "`h1` gives $|s \\cup t| + 2 = 15$, so $|s \\cup t| = 13$.
  `h2` gives $|u| \\leq |s \\cup t|$.
  `omega` combines them."
  omega

Conclusion "
The pattern: first compute the container's exact size, then bound
the subset.

| Step | Lemma | What it gave |
|---|---|---|
| 1 | `card_union_add_card_inter` | $|s \\cup t| + 2 = 6 + 9 = 15$ |
| 2 | `card_le_card` | $|u| \\leq |s \\cup t| = 13$ |

This is a **transfer** problem: you never saw this exact combination
in the Cardinality world, but the ingredients are familiar.
Inclusion-exclusion gives exact sizes; monotonicity turns exact sizes
into bounds.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
