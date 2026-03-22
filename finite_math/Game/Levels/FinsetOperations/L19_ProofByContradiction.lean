import Game.Metadata

World "FinsetOperations"
Level 19

Title "Proof by Contradiction"

Introduction "
# by_contra: Proof by Contradiction

Sometimes you need to prove something positive (`x ∈ t`) but your
hypotheses only give you negative information (`x ∉ s \\\\ t`). In
these cases, **proof by contradiction** is the right move.

**New tactic**: `by_contra hnt` on a goal `P` introduces `hnt : ¬P`
and changes the goal to `False`. You then derive `False` from
`hnt` and your other hypotheses.

Here's the setup: you know `x ∈ s` and `x ∉ s \\\\ t`. You need
`x ∈ t`. The idea: if `x ∉ t`, then `x ∈ s ∧ x ∉ t` would give
`x ∈ s \\\\ t`, contradicting `x ∉ s \\\\ t`.

Note: `simp` is disabled for this and the next two levels to ensure
you practice `by_contra` and manual proof construction.

**Your task**: From `x ∈ s` and `x ∉ s \\\\ t`, prove `x ∈ t`.
"

/-- If x is in s but not in s \ t, then x must be in t. -/
Statement (s t : Finset ℕ) (x : ℕ) (hs : x ∈ s) (h : x ∉ s \ t) : x ∈ t := by
  Hint "The goal is `x ∈ t`. You can't extract this directly from
  your hypotheses. Use `by_contra hnt` to assume `x ∉ t` and derive
  a contradiction."
  by_contra hnt
  Hint "Now `hnt : x ∉ t` (i.e., `¬(x ∈ t)`). You need to derive
  `False`. You have `h : x ∉ s \\\\ t`. If you can build a proof
  that `x ∈ s \\\\ t`, applying `h` to it gives `False`.
  Use `apply h`."
  apply h
  Hint "The goal is now `x ∈ s \\\\ t`. Use
  `rw [Finset.mem_sdiff]` to unfold it into a conjunction."
  rw [Finset.mem_sdiff]
  Hint (hidden := true) "The goal is `x ∈ s ∧ x ∉ t`.
  Use `exact ⟨hs, hnt⟩`."
  exact ⟨hs, hnt⟩

Conclusion "
You've used `by_contra` for the first time! The pattern:

1. **`by_contra hnt`** — assume `¬(goal)`, change goal to `False`
2. **Build a contradiction** — use `hnt` together with other hypotheses
   to construct something that violates a known fact

In this case: assuming `x ∉ t` let you build `x ∈ s \\\\ t` (from
`hs` and `hnt`), which contradicted `h : x ∉ s \\\\ t`.

`by_contra` is the tactic version of proof by contradiction — one of
the most fundamental techniques in mathematics. It's especially
useful when you need to extract positive information from negative
hypotheses.

In the next level, you'll use `by_contra` inside a more complex proof:
the double set difference identity.
"

NewTactic by_contra

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self sdiff_sup Finset.sdiff_inter_distrib_left and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right
