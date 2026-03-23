import Game.Metadata

World "FinsetOperations"
Level 13

Title "Intersection Commutativity"

Introduction "
# Proving a Set Identity with ext

Now you'll prove **intersection commutativity**: $s \\cap t = t \\cap s$.
The proof uses `.1`/`.2` and `⟨,⟩` from Level 9 to swap the conjunction
components in both directions.

**A note on notation**: Finset `∪` and `∩` are actually lattice
operations `⊔` and `⊓` under the hood. You may occasionally see `⊔` or
`⊓` in the infoview. This is just an alternative notation — the
membership lemmas (`mem_union`, `mem_inter`) work the same way.

**Your task**: Prove that $s \\cap t = t \\cap s$.
"

/-- Intersection is commutative. -/
Statement (s t : Finset ℕ) : s ∩ t = t ∩ s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Rewrite both intersection memberships:
  `rw [Finset.mem_inter, Finset.mem_inter]`.
  The first rewrite handles `x ∈ s ∩ t`, the second handles `x ∈ t ∩ s`."
  rw [Finset.mem_inter, Finset.mem_inter]
  Hint "The goal is `x ∈ s ∧ x ∈ t ↔ x ∈ t ∧ x ∈ s`. Use
  `constructor` to split the biconditional."
  constructor
  · Hint "**Commutativity pattern (conjunction)**: Swap the two
    components using `.1` and `.2` projections and `⟨,⟩` constructor.
    Given `h : x ∈ s ∧ x ∈ t`, build `⟨h.2, h.1⟩ : x ∈ t ∧ x ∈ s`.
    Try: `intro h; exact ⟨h.2, h.1⟩`."
    intro h
    exact ⟨h.2, h.1⟩
  · Hint "Same idea in reverse: `intro h; exact ⟨h.2, h.1⟩`."
    intro h
    exact ⟨h.2, h.1⟩

Conclusion "
You just proved an abstract set identity! The proof structure:

1. `ext x` — convert equality to element-wise `↔`
2. `rw [Finset.mem_inter, Finset.mem_inter]` — convert to logic
3. `constructor` — split the `↔`
4. Each direction: swap the conjunction components

The new moves:
- **`.1` and `.2`**: extract components from a conjunction hypothesis.
  If `h : P ∧ Q`, then `h.1 : P` and `h.2 : Q`.
- **`⟨a, b⟩`**: build a conjunction in one line. `⟨h.2, h.1⟩` builds
  a proof of `Q ∧ P` from `h : P ∧ Q`.

This is the power of `ext`: once you reduce a set equation to logic,
you can use purely logical reasoning. Union gives `∨`, intersection
gives `∧`, and the proof becomes a logic exercise.
"

/-- `Finset.inter_comm s t` proves `s ∩ t = t ∩ s`.

Intersection is commutative — the order of the arguments doesn't matter.
-/
TheoremDoc Finset.inter_comm as "Finset.inter_comm" in "Finset"

NewTheorem Finset.inter_comm

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right Finset.inter_left_comm Finset.inter_right_comm
