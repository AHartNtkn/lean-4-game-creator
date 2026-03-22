import Game.Metadata

World "FinsetOperations"
Level 6

Title "Subset Monotonicity"

Introduction "
# Union Makes Sets Bigger

You've seen subset (`⊆`) and union (`∪`) separately. Now let's connect
them: **every set is a subset of its union with anything else**.

$$s \\subseteq s \\cup t$$

This is intuitively obvious — if `x ∈ s`, then certainly
`x ∈ s ∨ x ∈ t` (by choosing the left disjunct), so `x ∈ s ∪ t`.

The proof combines two tools you already know:
- `Finset.subset_iff` from Level 5 (unfold `⊆` to `∀ x ∈ s, x ∈ s ∪ t`)
- `Finset.mem_union` from Level 1 (convert `x ∈ s ∪ t` to `x ∈ s ∨ x ∈ t`)

**Your task**: Prove that $s \\subseteq s \\cup t$.
"

/-- Every set is a subset of its union with another set. -/
Statement (s t : Finset ℕ) : s ⊆ s ∪ t := by
  Hint "Use `rw [Finset.subset_iff]` to unfold the subset relation."
  rw [Finset.subset_iff]
  Hint "Use `intro x hx` to introduce an element and its membership in `s`."
  intro x hx
  Hint "The goal is `x ∈ s ∪ t`. Use `rw [Finset.mem_union]` to convert
  to a disjunction, then choose `left`."
  rw [Finset.mem_union]
  Hint (hidden := true) "`left; exact hx`."
  left
  exact hx

Conclusion "
You've proved the **subset-union monotonicity** law: $s \\subseteq s \\cup t$.

The proof was short: unfold `⊆`, take any `x ∈ s`, unfold `∈ s ∪ t`
to `x ∈ s ∨ x ∈ t`, and choose `left`.

The **dual** fact is equally important: $s \\cap t \\subseteq s$.
Intersection makes sets *smaller*. The proof is similar: unfold `⊆`,
take `x ∈ s ∩ t`, unfold to `x ∈ s ∧ x ∈ t`, and project with `.1`.

These two facts — **union enlarges, intersection shrinks** — are the
structural foundation for cardinality inequalities you'll see later:
`card(s ∩ t) ≤ card(s) ≤ card(s ∪ t)`.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto ext
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right le_sup_left le_sup_right inf_le_left inf_le_right
