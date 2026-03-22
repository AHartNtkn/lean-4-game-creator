import Game.Metadata

World "FinsetOperations"
Level 10

Title "Empty Set Identity"

Introduction "
# Union with the Empty Set

Another set identity using `ext`: prove that
$s \\cup \\varnothing = s$.

Unioning with the empty set adds nothing — every element of `s ∪ ∅`
is either in `s` (which contributes) or in `∅` (which contributes
nothing, since `∅` has no elements).

After `ext x` and `rw [Finset.mem_union]`, the goal becomes:
$$x \\in s \\lor x \\in \\varnothing \\;\\longleftrightarrow\\; x \\in s$$

**Forward**: If `x ∈ s ∨ x ∈ ∅`, case-split. In the `x ∈ s` case,
done. In the `x ∈ ∅` case, this is impossible — recall from Finset
Basics that `Finset.notMem_empty x` proves `x ∉ ∅`.

**Backward**: If `x ∈ s`, choose `left`.

**Recall**: `exact absurd he (Finset.notMem_empty x)` closes a goal
when you have `he : x ∈ ∅`. The function `absurd` (from MeetFin) derives
anything from a proof and its negation: since `he` says `x ∈ ∅` and
`Finset.notMem_empty x` says `x ∉ ∅`, the contradiction closes the goal.

**Your task**: Prove that $s \\cup \\varnothing = s$.
"

/-- Union with the empty set is the identity: s ∪ ∅ = s. -/
Statement (s : Finset ℕ) : s ∪ ∅ = s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `rw [Finset.mem_union]` to unfold the union."
  rw [Finset.mem_union]
  Hint "The goal is `x ∈ s ∨ x ∈ ∅ ↔ x ∈ s`.
  Use `constructor` to split the biconditional."
  constructor
  · Hint "Use `intro h` then `cases h with` to split the disjunction."
    intro h
    cases h with
    | inl hs =>
      Hint (hidden := true) "`exact hs`."
      exact hs
    | inr he =>
      Hint (hidden := true) "You have `he : x ∈ ∅`, but the empty set
      has no elements. Use `exact absurd he (Finset.notMem_empty x)`."
      exact absurd he (Finset.notMem_empty x)
  · Hint "If `x ∈ s`, choose the left side:
    `intro hs; left; exact hs`."
    intro hs
    left
    exact hs

Conclusion "
You've proved the **union identity law**: $s \\cup \\varnothing = s$.

The key observation: the `x ∈ ∅` case is *vacuously true* — it can
never actually occur, so you can dismiss it with `absurd`.

The dual identity $s \\cap \\varnothing = \\varnothing$ also holds.
After `ext x; rw [Finset.mem_inter]`, the goal becomes
`x ∈ s ∧ x ∈ ∅ ↔ x ∈ ∅`. The forward direction extracts `x ∈ ∅`
via `.2`. The backward direction is vacuously true (same `absurd` move).

These identity laws are the 'base cases' of set algebra — they'll
reappear when you study cardinality: `card(s ∪ ∅) = card(s)` and
`card(s ∩ ∅) = 0`.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_empty Finset.empty_union sup_bot_eq bot_sup_eq
