import Game.Metadata

World "FinsetOperations"
Level 23

Title "Distributivity"

Introduction "
# Union Distributes Over Intersection

You'll prove an important set identity using the **unfold-to-logic**
recipe:

$$(s \\cup t) \\cap u = (s \\cap u) \\cup (t \\cap u)$$

This is **right distributivity** of union over intersection — the
set-theoretic analogue of $a \\cdot (b + c) = a \\cdot b + a \\cdot c$.

After `ext x; simp only [Finset.mem_inter, Finset.mem_union]`,
the goal becomes pure propositional logic:

$$(x \\in s \\lor x \\in t) \\land x \\in u \\;\\longleftrightarrow\\; (x \\in s \\land x \\in u) \\lor (x \\in t \\land x \\in u)$$

The forward direction: extract the `∨` from the left `∧`, case-split,
and rebuild. The backward direction: case-split the `∨`, extract the
`∧` components, and rebuild.

**Your task**: Prove distributivity.
"

/-- Union distributes over intersection. -/
Statement (s t u : Finset ℕ) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) := by
  Hint "Start with `ext x` to convert the set equality into an
  element-wise biconditional."
  ext x
  Hint "Use `simp only [Finset.mem_inter, Finset.mem_union]` to
  unfold all memberships into pure logic.

  **Alternative**: you can use `rw` chains instead:
  `rw [Finset.mem_inter]` then `rw [Finset.mem_union]` etc."
  simp only [Finset.mem_inter, Finset.mem_union]
  Hint "The goal is now pure logic:
  `(x ∈ s ∨ x ∈ t) ∧ x ∈ u ↔ (x ∈ s ∧ x ∈ u) ∨ (x ∈ t ∧ x ∈ u)`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: (x ∈ s ∨ x ∈ t) ∧ x ∈ u → (x ∈ s ∧ x ∈ u) ∨ (x ∈ t ∧ x ∈ u)
  · Hint "Use `intro h`. Then `h.1` is the `∨` part and `h.2` is `x ∈ u`.
    Case-split on `h.1` using `cases h.1 with`."
    intro h
    Hint (hidden := true) "`cases h.1 with` splits `h.1 : x ∈ s ∨ x ∈ t` into
    two cases. In each case, build the conjunction with `⟨..., h.2⟩`
    and choose `left` or `right`."
    cases h.1 with
    | inl hs =>
      Hint (hidden := true) "You have `hs : x ∈ s` and `h.2 : x ∈ u`.
      The goal is the `∨`. Choose `left` and build the conjunction:
      `left; exact ⟨hs, h.2⟩`."
      left
      exact ⟨hs, h.2⟩
    | inr ht =>
      Hint (hidden := true) "You have `ht : x ∈ t` and `h.2 : x ∈ u`.
      Choose `right` and build the conjunction:
      `right; exact ⟨ht, h.2⟩`."
      right
      exact ⟨ht, h.2⟩
  -- Backward: (x ∈ s ∧ x ∈ u) ∨ (x ∈ t ∧ x ∈ u) → (x ∈ s ∨ x ∈ t) ∧ x ∈ u
  · Hint "Use `intro h`. Then case-split on `h` (which is a `∨`) using
    `cases h with`."
    intro h
    Hint (hidden := true) "`cases h with` gives two cases. In each,
    extract `.1` and `.2` from the conjunction. Then build the goal
    with `constructor` and `left`/`right`."
    cases h with
    | inl hsu =>
      Hint (hidden := true) "You have `hsu : x ∈ s ∧ x ∈ u`. The goal
      is a conjunction. Use `constructor`, then `left; exact hsu.1`
      for the first part and `exact hsu.2` for the second."
      constructor
      · left; exact hsu.1
      · exact hsu.2
    | inr htu =>
      Hint (hidden := true) "You have `htu : x ∈ t ∧ x ∈ u`. Use
      `constructor`, then `right; exact htu.1` and `exact htu.2`."
      constructor
      · right; exact htu.1
      · exact htu.2

Conclusion "
You've proved **distributivity**: $(s \\cup t) \\cap u = (s \\cap u) \\cup (t \\cap u)$.

The proof followed the unfold-to-logic recipe perfectly:
1. `ext x` reduced the set equality to logic
2. `simp only [mem_inter, mem_union]` converted to pure propositions
3. `constructor` + `cases` + `left`/`right` handled the logic

The propositional content was $(A \\lor B) \\land C \\iff (A \\land C) \\lor (B \\land C)$
— conjunction distributes over disjunction.

Next: the **dual** distributivity law, where union and intersection
swap roles. Then the boss, which brings in set difference.
"

DisabledTactic trivial «decide» native_decide aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm Finset.union_inter_distrib_right Finset.union_inter_distrib_left Finset.union_self Finset.inter_self inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left sup_inf_self inf_sup_self Finset.union_inter_cancel_left Finset.inter_union_cancel_left sdiff_sup and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_left_comm Finset.union_right_comm Finset.inter_left_comm Finset.inter_right_comm
