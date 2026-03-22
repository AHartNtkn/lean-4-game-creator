import Game.Metadata

World "FinsetOperations"
Level 15

Title "Union Associativity"

Introduction "
# Associativity: Grouping Doesn't Matter

You've proved commutativity (order doesn't matter) and idempotency
(repeating doesn't matter). Now prove **associativity**: grouping
doesn't matter.

$$(s \\cup t) \\cup u = s \\cup (t \\cup u)$$

After `ext x` and unfolding all unions with `rw [Finset.mem_union]`
(applied multiple times), the goal becomes:

$$(x \\in s \\lor x \\in t) \\lor x \\in u \\;\\longleftrightarrow\\; x \\in s \\lor (x \\in t \\lor x \\in u)$$

This is **associativity of disjunction**: $(P \\lor Q) \\lor R \\iff P \\lor (Q \\lor R)$.

Both directions require nested `cases` to split the outer disjunction,
then the inner one. In each leaf case, rebuild with the correct nesting
of `left`/`right`.

**Your task**: Prove that $(s \\cup t) \\cup u = s \\cup (t \\cup u)$.
"

/-- Union is associative. -/
Statement (s t u : Finset ℕ) : (s ∪ t) ∪ u = s ∪ (t ∪ u) := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Unfold all unions. Use `rw [Finset.mem_union]` repeatedly
  (four times total) to unfold each `∪` into `∨`.

  Alternatively, use `rw [Finset.mem_union, Finset.mem_union,
  Finset.mem_union, Finset.mem_union]` in one step."
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_union, Finset.mem_union]
  Hint "The goal is `(x ∈ s ∨ x ∈ t) ∨ x ∈ u ↔ x ∈ s ∨ (x ∈ t ∨ x ∈ u)`.
  Use `constructor` to split the biconditional."
  constructor
  -- Forward: (x ∈ s ∨ x ∈ t) ∨ x ∈ u → x ∈ s ∨ (x ∈ t ∨ x ∈ u)
  · Hint "**Associativity pattern**: Nested case-splits. Split the outer
    `∨` first, then the inner `∨`. In each leaf case, rebuild with
    the correct nesting of `left`/`right`.
    Use `intro h` then `cases h with` to split the outer disjunction."
    intro h
    Hint (hidden := true) "`cases h with` gives `| inl hst => ...` (where
    `hst : x ∈ s ∨ x ∈ t`) and `| inr hu => ...` (where `hu : x ∈ u`).
    In the `inl` case, split `hst` with another `cases`.
    In the `inr` case, `right; right; exact hu`."
    cases h with
    | inl hst =>
      Hint (hidden := true) "Split `hst : x ∈ s ∨ x ∈ t` with `cases hst with`.
      If `x ∈ s`: `left; exact hs`.
      If `x ∈ t`: `right; left; exact ht`."
      cases hst with
      | inl hs => left; exact hs
      | inr ht => right; left; exact ht
    | inr hu => right; right; exact hu
  -- Backward: x ∈ s ∨ (x ∈ t ∨ x ∈ u) → (x ∈ s ∨ x ∈ t) ∨ x ∈ u
  · Hint "Same pattern: `intro h; cases h with`."
    intro h
    Hint (hidden := true) "In the `inl` case (`hs : x ∈ s`): `left; left; exact hs`.
    In the `inr` case, split `htu : x ∈ t ∨ x ∈ u` with another `cases`.
    If `x ∈ t`: `left; right; exact ht`.
    If `x ∈ u`: `right; exact hu`."
    cases h with
    | inl hs => left; left; exact hs
    | inr htu =>
      cases htu with
      | inl ht => left; right; exact ht
      | inr hu => right; exact hu

Conclusion "
Union is **associative**: $(s \\cup t) \\cup u = s \\cup (t \\cup u)$.

The proof required **nested case-splitting** — the outer `cases` splits
the top-level `∨`, and an inner `cases` splits the nested `∨`. Each leaf
case rebuilds the goal with the correct nesting of `left`/`right`.

With commutativity (Level 12-13), idempotency (Level 9, 11), identity
(Level 10), and now associativity, you've covered the fundamental
algebraic laws for union. These same laws hold for intersection (with
`∧` in place of `∨`) — the **dual** identity
$(s \\cap t) \\cap u = s \\cap (t \\cap u)$ has a structurally identical
proof using `.1`/`.2` and `⟨,⟩` instead of `cases` and `left`/`right`.

Together, these laws make `Finset` with `∪` and `∩` a **lattice** — a
structure you'll see more of in the next level.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_idem sup_idem inf_assoc sup_assoc le_antisymm inf_sup_right inf_sup_left sup_inf_right sup_inf_left Finset.inter_self Finset.union_self and_comm or_comm or_and_right or_and_left and_or_right and_or_left not_or inf_le_left inf_le_right le_sup_left le_sup_right or_assoc Finset.union_assoc Finset.union_left_comm Finset.union_right_comm
