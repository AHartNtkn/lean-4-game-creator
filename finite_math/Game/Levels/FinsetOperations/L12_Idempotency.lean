import Game.Metadata

World "FinsetOperations"
Level 12

Title "Idempotency"

Introduction "
# Union is Idempotent

Here's the simplest non-trivial set identity: $s \\cup s = s$.
Unioning a set with itself adds nothing.

After `ext x` and `rw [Finset.mem_union]`, the goal becomes:
$$x \\in s \\lor x \\in s \\;\\longleftrightarrow\\; x \\in s$$

**Forward**: If `x ∈ s ∨ x ∈ s`, case-split. Both cases give `x ∈ s`.

**Backward**: If `x ∈ s`, choose `left` (or `right` — both work).

This is structurally simpler than commutativity: instead of *swapping*
the components, both branches produce the *same* result.

**Experienced learners**: Levels 12-15 (idempotency, commutativity,
associativity) are practice applications of the `ext` + unfold +
logic recipe from Levels 9-11. If you've internalized the recipe,
you can skip ahead to Level 16 (lattice notation) without missing
any new concepts. These levels exist for learners who want more
repetition before moving on.

**Your task**: Prove that $s \\cup s = s$.
"

/-- Union is idempotent: s ∪ s = s. -/
Statement (s : Finset ℕ) : s ∪ s = s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `rw [Finset.mem_union]` to unfold the union."
  rw [Finset.mem_union]
  Hint "The goal is `x ∈ s ∨ x ∈ s ↔ x ∈ s`.
  Use `constructor` to split the biconditional."
  constructor
  · Hint "**Idempotency pattern (forward)**: Both sides of the `∨`
    say the same thing (`x ∈ s`), so both cases produce `x ∈ s`.
    Use `intro h` then `cases h with`."
    intro h
    Hint (hidden := true) "Both cases give `x ∈ s`:
    `| inl hs => exact hs` and `| inr hs => exact hs`."
    cases h with
    | inl hs => exact hs
    | inr hs => exact hs
  · Hint "If `x ∈ s`, choose either side:
    `intro hs; left; exact hs`."
    intro hs
    left
    exact hs

Conclusion "
$s \\cup s = s$ — union is **idempotent** (applying it twice gives
the same result).

The proof was even simpler than commutativity: both cases of the
forward direction produce the same output. This is the set-level
version of $P \\lor P \\iff P$.

The **dual** ($s \\cap s = s$) was Level 9 — you already proved it!
Union idempotency uses `cases` + both branches identical; intersection
idempotency uses `.1` projection + `⟨hs, hs⟩` duplication.

Next: commutativity — where you swap the two sides instead of
collapsing them.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right Finset.union_self Finset.inter_self sup_idem inf_idem Finset.union_empty Finset.empty_union sup_bot_eq bot_sup_eq Finset.union_idempotent or_self
