import Game.Metadata

World "PsetCardinality"
Level 4

Title "Disjoint Triple Union"

Introduction "
# Three Disjoint Sets

You have three finsets that are pairwise disjoint, with known sizes.

**Your task**: Compute the cardinality of their three-way union.

You learned how to compute the cardinality of a disjoint union of
two sets. Three sets means applying the same idea twice — first
combine two sets, then add the third.

Think about what hypotheses you need for each application.
"

/-- The union of three pairwise disjoint finsets has cardinality equal to the sum. -/
Statement (s₁ s₂ s₃ : Finset ℕ)
    (h12 : Disjoint s₁ s₂) (h123 : Disjoint (s₁ ∪ s₂) s₃)
    (hs₁ : s₁.card = 4) (hs₂ : s₂.card = 5) (hs₃ : s₃.card = 3) :
    (s₁ ∪ s₂ ∪ s₃).card = 12 := by
  Hint "You need `card_union_of_disjoint` applied twice — once for
  the inner union `s₁ ∪ s₂`, and once for the outer union with `s₃`.
  Collect both cardinality facts, then let `omega` finish."
  Hint (hidden := true) "The two `have` statements you need:
  `have h1 := Finset.card_union_of_disjoint h12`
  `have h2 := Finset.card_union_of_disjoint h123`
  Then `omega`."
  have h1 := Finset.card_union_of_disjoint h12
  Hint "`h1 : (s₁ ∪ s₂).card = s₁.card + s₂.card`.
  Now apply `card_union_of_disjoint` again for the outer union."
  Hint (hidden := true) "Try `have h2 := Finset.card_union_of_disjoint h123`."
  have h2 := Finset.card_union_of_disjoint h123
  Hint "`h2 : (s₁ ∪ s₂ ∪ s₃).card = (s₁ ∪ s₂).card + s₃.card`.
  Combined with h1, hs₁, hs₂, and hs₃, `omega` finishes:
  $(4 + 5) + 3 = 12$."
  omega

Conclusion "
Two applications of `card_union_of_disjoint` give:

$$|s_1 \\cup s_2 \\cup s_3| = |s_1 \\cup s_2| + |s_3| = (|s_1| + |s_2|) + |s_3| = 4 + 5 + 3 = 12$$

With two sets, one application sufficed. With three, you needed two.
With four sets you'd need three. See the pattern?

In Phase 4, you'll learn the **big sum operator** `∑`, which
generalizes this: for a family of pairwise disjoint sets,
$|\\bigcup_i s_i| = \\sum_i |s_i|$. That single lemma replaces an
arbitrary number of `card_union_of_disjoint` applications.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
