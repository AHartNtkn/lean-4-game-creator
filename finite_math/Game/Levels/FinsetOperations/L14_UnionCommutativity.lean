import Game.Metadata

World "FinsetOperations"
Level 14

Title "Union Commutativity"

Introduction "
# ext with Disjunction

In Level 12 you proved $s \\cap t = t \\cap s$ — intersection commutativity.
The proof used `ext`, then swapped conjunction components with `.1`/`.2`
and `⟨h.2, h.1⟩`.

Now try the dual: **union commutativity**, $s \\cup t = t \\cup s$.

After `ext x` and rewriting with `mem_union`, the goal becomes:
$$x \\in s \\lor x \\in t \\;\\longleftrightarrow\\; x \\in t \\lor x \\in s$$

This time you're swapping *disjunction* components, not conjunction.
You can't use `.1`/`.2` on a disjunction — instead, you need `cases`
to split it, then `left`/`right` to rebuild in the other order.

**Your task**: Prove that $s \\cup t = t \\cup s$.
"

/-- Union is commutative. -/
Statement (s t : Finset ℕ) : s ∪ t = t ∪ s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Rewrite both union memberships:
  `rw [Finset.mem_union, Finset.mem_union]`."
  rw [Finset.mem_union, Finset.mem_union]
  Hint "The goal is `x ∈ s ∨ x ∈ t ↔ x ∈ t ∨ x ∈ s`. Use
  `constructor` to split the biconditional."
  constructor
  · Hint "**Commutativity pattern (disjunction)**: Case-split on `∨`,
    then rebuild with the sides swapped using `left`/`right`.
    Use `intro h` then `cases h with` to split on which side holds."
    intro h
    Hint (hidden := true) "`cases h with` gives `| inl hs => ...`
    and `| inr ht => ...`. In the first case, choose `right`;
    in the second, choose `left`."
    cases h with
    | inl hs =>
      Hint (hidden := true) "You have `hs : x ∈ s`. The goal needs
      `x ∈ t ∨ x ∈ s`, so choose `right`: `right; exact hs`."
      right; exact hs
    | inr ht =>
      Hint (hidden := true) "`left; exact ht`."
      left; exact ht
  · Hint "Same pattern in reverse: `intro h; cases h with`."
    intro h
    Hint (hidden := true) "Swap the sides again: `inl` case gets
    `right`, `inr` case gets `left`."
    cases h with
    | inl ht =>
      right; exact ht
    | inr hs =>
      left; exact hs

Conclusion "
You've now proved commutativity for both intersection (∧-swapping)
and union (∨-swapping). Compare the two patterns:

**Intersection commutativity** (Level 12):
- After ext + rewrite: `x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s`
- Swap conjuncts: `intro h; exact ⟨h.2, h.1⟩`

**Union commutativity** (this level):
- After ext + rewrite: `x ∈ s ∨ x ∈ t ↔ x ∈ t ∨ x ∈ s`
- Swap disjuncts: `intro h; cases h with | inl => right | inr => left`

The key difference: conjunctions let you project (`.1`/`.2`), but
disjunctions require case-splitting (`cases`) and rebuilding
(`left`/`right`). Both patterns appear in the boss.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_left_comm Finset.union_right_comm
