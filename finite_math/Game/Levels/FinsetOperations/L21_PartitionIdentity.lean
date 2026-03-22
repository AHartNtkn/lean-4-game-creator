import Game.Metadata

World "FinsetOperations"
Level 21

Title "The Partition Identity"

Introduction "
# Every Set Splits Into Two Pieces

Here's a fundamental identity: every finset `s` splits into two
disjoint pieces relative to any other finset `t`:

$$s = (s \\setminus t) \\cup (s \\cap t)$$

The left piece `s \\ t` contains elements of `s` that are NOT in `t`.
The right piece `s ∩ t` contains elements of `s` that ARE in `t`.
Together they account for every element of `s`.

This is the **partition identity**: it decomposes `s` into
'the part outside `t`' and 'the part inside `t`.'

After `ext x` and rewriting with `Finset.mem_union`, `Finset.mem_sdiff`,
and `Finset.mem_inter`, the goal becomes:

$$x \\in s \\;\\longleftrightarrow\\; (x \\in s \\land x \\notin t) \\lor (x \\in s \\land x \\in t)$$

**Forward**: If `x ∈ s`, check whether `x ∈ t` or `x ∉ t` using
`by_cases`. In either case, you can build the appropriate side of
the disjunction.

**Backward**: Case-split on the `∨`. In both cases, `.1` gives `x ∈ s`.

**Your task**: Prove the partition identity.
"

/-- Every finset splits: s = (s \ t) ∪ (s ∩ t). -/
Statement (s t : Finset ℕ) : s \ t ∪ s ∩ t = s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Unfold all operations with
  `rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]`."
  rw [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
  Hint "The goal is
  `(x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∈ t) ↔ x ∈ s`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∈ t) → x ∈ s
  · Hint "Both sides of the `∨` contain `x ∈ s` as the first
    component. Case-split on `h` and use `.1` in both cases."
    Hint (hidden := true) "`intro h; cases h with | inl h | inr h` then `exact h.1` in both branches."
    intro h
    cases h with
    | inl h => exact h.1
    | inr h => exact h.1
  -- Backward: x ∈ s → (x ∈ s ∧ x ∉ t) ∨ (x ∈ s ∧ x ∈ t)
  · Hint "You have `hs : x ∈ s` and need to choose which side of
    the disjunction to prove. The deciding factor is whether `x ∈ t`
    or `x ∉ t`. Use `by_cases hxt : x ∈ t` to split on this."
    intro hs
    Hint (hidden := true) "`by_cases hxt : x ∈ t`.
    If `x ∈ t`: `right; exact ⟨hs, hxt⟩`.
    If `x ∉ t`: `left; exact ⟨hs, hxt⟩`."
    by_cases hxt : x ∈ t
    · right; exact ⟨hs, hxt⟩
    · left; exact ⟨hs, hxt⟩

Conclusion "
You've proved the **partition identity**: $s = (s \\setminus t) \\cup (s \\cap t)$.

Every finset `s` decomposes into exactly two pieces relative to `t`:
- Elements in `s` but not in `t` (the set difference)
- Elements in both `s` and `t` (the intersection)

This identity has a powerful numerical consequence. Since
`s \\ t` and `s ∩ t` are **disjoint** (no element can satisfy
both `x ∉ t` and `x ∈ t`), taking cardinalities gives:

$$|s| = |s \\setminus t| + |s \\cap t|$$

This is exactly `Finset.card_sdiff_add_card_inter`, which you'll
use in the Cardinality world for **complement counting**. Now you
know *why* complement counting works — it follows from this
partition identity.

Note: This level used `by_cases` for the first time in this world.
`by_cases hxt : x ∈ t` creates two subgoals: one where `hxt : x ∈ t`
and one where `hxt : x ∉ t`. It's the tool for deciding which side
of a disjunction to prove when the deciding condition is a proposition.
"

NewTactic by_cases

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self sdiff_sup Finset.sdiff_inter_distrib_left sup_inf_self inf_sup_self Finset.union_inter_cancel_left Finset.inter_union_cancel_left and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or sdiff_sdiff_right_self inf_le_left inf_le_right le_sup_left le_sup_right Finset.sdiff_union_inter sdiff_union_inf
