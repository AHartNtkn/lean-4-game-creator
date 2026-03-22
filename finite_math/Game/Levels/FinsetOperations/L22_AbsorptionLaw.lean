import Game.Metadata

World "FinsetOperations"
Level 22

Title "Absorption Law"

Introduction "
# The Absorption Law

Here's a surprising identity: $s \\cup (s \\cap t) = s$. The intersection
with `t` adds nothing — `s` already contains everything in `s ∩ t`.

This is the **absorption law**, one of the fundamental lattice identities.
Unlike commutativity or De Morgan (where both directions have similar
structure), this proof is **asymmetric**: one direction is trivial,
the other requires a case split.

After `ext x` and rewriting with `Finset.mem_union` and
`Finset.mem_inter`, the goal becomes:
$$x \\in s \\lor (x \\in s \\land x \\in t) \\;\\longleftrightarrow\\; x \\in s$$

**Forward** ($\\Rightarrow$): If `x ∈ s ∨ (x ∈ s ∧ x ∈ t)`, case-split.
In both cases, `x ∈ s` — either directly or via `.1`.

**Backward** ($\\Leftarrow$): If `x ∈ s`, choose `left`.

Note: `simp` is disabled for this level to ensure you practice the
manual asymmetric proof structure.

**Your task**: Prove the absorption law.
"

/-- Absorption: s ∪ (s ∩ t) = s. -/
Statement (s t : Finset ℕ) : s ∪ (s ∩ t) = s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `rw [Finset.mem_union, Finset.mem_inter]`
  to unfold the operations into logic."
  rw [Finset.mem_union, Finset.mem_inter]
  Hint "The goal is `x ∈ s ∨ (x ∈ s ∧ x ∈ t) ↔ x ∈ s`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: x ∈ s ∨ (x ∈ s ∧ x ∈ t) → x ∈ s
  · Hint "Use `intro h` then `cases h with` to split the disjunction."
    intro h
    Hint (hidden := true) "In both cases, `x ∈ s` follows.
    For `| inl hs =>`, `exact hs`.
    For `| inr hst =>`, `exact hst.1`."
    cases h with
    | inl hs => exact hs
    | inr hst => exact hst.1
  -- Backward: x ∈ s → x ∈ s ∨ (x ∈ s ∧ x ∈ t)
  · Hint "If `x ∈ s`, choose the left side of the disjunction:
    `intro hs; left; exact hs`."
    intro hs
    left
    exact hs

Conclusion "
The absorption law has a beautifully asymmetric proof:
- **Forward**: both branches of the `∨` give `x ∈ s` — one directly,
  one via `.1` projection
- **Backward**: immediate by `left`

This asymmetry is the distinguishing feature: unlike commutativity
(where both directions are the same swap) or distributivity (where both
directions have similar case-split structure), absorption has one
'trivial' direction and one 'case-split' direction.

The absorption law says that intersecting with `t` and then unioning
back with `s` adds nothing — `s` already 'absorbs' `s ∩ t`.

The **dual absorption law** `s ∩ (s ∪ t) = s` also holds. After
`ext x; rw [Finset.mem_inter, Finset.mem_union]`, the goal becomes
`x ∈ s ∧ (x ∈ s ∨ x ∈ t) ↔ x ∈ s`. The forward direction uses
`.1` to project out `x ∈ s` from the conjunction. The backward
direction uses `⟨hs, Or.inl hs⟩` to build the conjunction. Same
moves, swapped roles of ∧ and ∨.

Next up: the partition identity, then distributivity, and finally
the boss.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto push_neg
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self sdiff_sup Finset.sdiff_inter_distrib_left sup_inf_self inf_sup_self Finset.union_inter_cancel_left Finset.inter_union_cancel_left and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or sdiff_sdiff_right_self inf_le_left inf_le_right le_sup_left le_sup_right
