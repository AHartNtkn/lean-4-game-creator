import Game.Metadata

World "PsetCardinality"
Level 5

Title "List Insertion Cardinality"

Introduction "
# From Lists to Finset Cardinality

You have a list `l` with no duplicates and known length, plus an
element `a` not in `l`.

**Your task**: Prove that `(a :: l).toFinset` has exactly
`l.length + 1` elements.

This combines tools from two worlds:
- **Abstraction Ladder**: converting between lists and finsets
- **Cardinality**: counting what insertion does

The tricky step: the insertion cardinality lemma needs
`a ∉ l.toFinset`, but you have `a ∉ l`. You'll need to bridge
between list membership and finset membership.
"

/-- Prepending a fresh element to a nodup list increases the toFinset card by 1. -/
Statement (l : List ℕ) (a : ℕ) (hnd : l.Nodup) (hlen : l.length = 4)
    (hnotmem : a ∉ l) :
    (a :: l).toFinset.card = 5 := by
  Hint "Start by unfolding `toFinset` on the cons'd list:
  `rw [List.toFinset_cons]` turns `(a :: l).toFinset` into
  `insert a l.toFinset`."
  rw [List.toFinset_cons]
  Hint "The goal is `(insert a l.toFinset).card = 5`. You need
  `a ∉ l.toFinset` to apply `card_insert_of_notMem`. But you have
  `hnotmem : a ∉ l`. Use `mem_toFinset` to convert."
  Hint (hidden := true) "Try:
  `have hf : a ∉ l.toFinset := by rw [List.mem_toFinset]; exact hnotmem`"
  have hf : a ∉ l.toFinset := by rw [List.mem_toFinset]; exact hnotmem
  Hint "Now apply `card_insert_of_notMem` with `hf`."
  Hint (hidden := true) "Try `rw [Finset.card_insert_of_notMem hf]`."
  rw [Finset.card_insert_of_notMem hf]
  Hint "The goal is `l.toFinset.card + 1 = 5`. Use
  `toFinset_card_of_nodup` to convert the finset card to the list
  length, then substitute `hlen`."
  Hint (hidden := true) "Try `rw [List.toFinset_card_of_nodup hnd, hlen]`."
  rw [List.toFinset_card_of_nodup hnd, hlen]

Conclusion "
Four tools from two worlds, combined on a fresh surface:

| Step | Tool | Source |
|---|---|---|
| 1 | `toFinset_cons` | Abstraction Ladder |
| 2 | `mem_toFinset` | Abstraction Ladder |
| 3 | `card_insert_of_notMem` | Cardinality |
| 4 | `toFinset_card_of_nodup` | Abstraction Ladder |

The key move was step 2: converting `a ∉ l` to `a ∉ l.toFinset`.
The `mem_toFinset` iff works under negation — `rw [mem_toFinset]`
inside a `¬(...)` goal replaces `a ∈ l.toFinset` with `a ∈ l`,
leaving `a ∉ l` which matches the hypothesis.

This cross-world combination is the point of a problem set:
individual skills from separate lectures must now work together.
"

TheoremTab "Card"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf
DisabledTheorem sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right le_antisymm sup_eq_left inf_eq_left sup_eq_right inf_eq_right Finset.union_comm Finset.inter_comm
