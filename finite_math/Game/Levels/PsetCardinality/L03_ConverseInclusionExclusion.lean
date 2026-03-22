import Game.Metadata

World "PsetCardinality"
Level 3

Title "Converse Inclusion-Exclusion"

Introduction "
# Computing Intersection from Union

You've applied inclusion-exclusion **forward**: given individual sizes
and overlap, compute the union. Now apply it **backward**.

**Given**: $|s \\cup t| = 11$, $|s| = 7$, $|t| = 8$.

**Your task**: Compute $|s \\cap t|$.

The same inclusion-exclusion identity works in both directions.
Rearranging: $|s \\cap t| = |s| + |t| - |s \\cup t| = 7 + 8 - 11 = 4$.

Collect the inclusion-exclusion fact and let `omega` do the algebra.
"

/-- Compute the intersection size from the union size via inclusion-exclusion. -/
Statement (s t : Finset ℕ) (hst : (s ∪ t).card = 11)
    (hs : s.card = 7) (ht : t.card = 8) :
    (s ∩ t).card = 4 := by
  Hint "Same lemma as Level 2 — but now you're solving for the
  intersection instead of bounding the union."
  Hint (hidden := true) "Try `have h := Finset.card_union_add_card_inter s t`
  then `omega`."
  have h := Finset.card_union_add_card_inter s t
  Hint "`h : (s \\cup t).card + (s \\cap t).card = s.card + t.card`.
  With the hypotheses, this gives $11 + |s \\cap t| = 15$.
  `omega` solves for $|s \\cap t| = 4$."
  omega

Conclusion "
The same inclusion-exclusion identity, applied in the reverse direction:

$$|s \\cap t| = |s| + |t| - |s \\cup t| = 7 + 8 - 11 = 4$$

This is the more common real-world application: you know how many
people study math, how many study physics, and how many study at
least one — how many study both?

The algebraic rearrangement is trivial (omega handles it), but the
problem-solving skill of recognizing inclusion-exclusion applied
**backward** is distinct from recognizing it forward.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
