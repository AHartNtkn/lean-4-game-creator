import Game.Metadata

World "FinsetOperations"
Level 11

Title "Disjoint Finsets"

Introduction "
# When Two Sets Share Nothing

Two sets are **disjoint** when they share no elements — their
intersection is empty: $s \\cap t = \\varnothing$.

This concept is fundamental to counting: when you compute
$|s \\cup t|$, the formula simplifies from $|s| + |t| - |s \\cap t|$
to just $|s| + |t|$ when $s$ and $t$ are disjoint.

**Your task**: Given a hypothesis that no element belongs to both
$s$ and $t$, prove $s \\cap t = \\varnothing$.

The proof uses the same `ext` recipe: reduce the equality to
element-wise reasoning, then use the hypothesis to close each case.
"

/-- If no element belongs to both sets, their intersection is empty. -/
Statement (s t : Finset ℕ) (h : ∀ x, x ∈ s → x ∉ t) : s ∩ t = ∅ := by
  Hint "Reduce the equality to element-wise reasoning with `ext x`,
  then `constructor`."
  ext x
  constructor
  · Hint "If `x ∈ s ∩ t`, unfold the intersection to get `x ∈ s` and
    `x ∈ t`. The hypothesis `h` says these are contradictory."
    intro hx
    rw [Finset.mem_inter] at hx
    Hint (hidden := true) "You have `hx.1 : x ∈ s` and `hx.2 : x ∈ t`.
    Apply `h x hx.1` to get `x ∉ t`, then
    `exact absurd hx.2 (h x hx.1)`."
    exact absurd hx.2 (h x hx.1)
  · Hint (hidden := true) "You have `hx : x ∈ ∅`, which is impossible.
    Use `exact absurd hx (Finset.notMem_empty x)`."
    intro hx
    exact absurd hx (Finset.notMem_empty x)

Conclusion "
Two sets are **disjoint** when $s \\cap t = \\varnothing$ — they share
no elements.

The proof pattern: `ext` reduces the equality to membership, the forward
direction contradicts the shared-element assumption, and the backward
direction is vacuously true (nothing belongs to $\\varnothing$).

This concept will become essential when you study cardinality:
**disjoint union** ($s \\cap t = \\varnothing$) means
$|s \\cup t| = |s| + |t|$ with no overlap to subtract.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right Finset.inter_self Finset.union_self inf_idem sup_idem Finset.union_empty Finset.empty_union sup_bot_eq bot_sup_eq Finset.disjoint_left Finset.disjoint_right Finset.not_disjoint_iff Finset.inter_eq_empty Finset.disjoint_iff_inter_eq_empty
