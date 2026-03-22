import Game.Metadata

World "FinsetOperations"
Level 9

Title "Intersection Idempotency"

Introduction "
# Your First ext Identity: s ∩ s = s

The simplest set identity you can prove with `ext`: intersecting a
set with itself gives back the same set.

After `ext x` and `rw [Finset.mem_inter]`, the goal becomes:
$$x \\in s \\land x \\in s \\;\\longleftrightarrow\\; x \\in s$$

**New notation**: `.1` and `.2` on conjunction hypotheses.

When you have `h : P ∧ Q`, you can extract:
- `h.1` gives the first component (`P`)
- `h.2` gives the second component (`Q`)

And to *build* a conjunction, use anonymous constructors:
`⟨proof_of_P, proof_of_Q⟩` is shorthand for `And.intro proof_of_P proof_of_Q`.

**Forward**: given `h : x ∈ s ∧ x ∈ s`, project with `h.1`.

**Backward**: given `hs : x ∈ s`, duplicate with `⟨hs, hs⟩`.

**Your task**: Prove that $s \\cap s = s$.
"

/-- Intersection is idempotent: s ∩ s = s. -/
Statement (s : Finset ℕ) : s ∩ s = s := by
  Hint "Start with `ext x` to convert the equality into a
  membership biconditional."
  ext x
  Hint "Use `rw [Finset.mem_inter]` to unfold the intersection."
  rw [Finset.mem_inter]
  Hint "The goal is `x ∈ s ∧ x ∈ s ↔ x ∈ s`.
  Use `constructor` to split the biconditional."
  constructor
  · Hint "Given `h : x ∈ s ∧ x ∈ s`, you need `x ∈ s`.
    Use `intro h` and then `exact h.1` to project the first component."
    intro h
    Hint (hidden := true) "`exact h.1` — the `.1` projection extracts
    the first component of the conjunction."
    exact h.1
  · Hint "Given `hs : x ∈ s`, you need `x ∈ s ∧ x ∈ s`.
    Use `intro hs` and then `exact ⟨hs, hs⟩` to build the conjunction."
    intro hs
    Hint (hidden := true) "`exact ⟨hs, hs⟩` — the anonymous constructor
    builds the conjunction by duplicating the same proof."
    exact ⟨hs, hs⟩

Conclusion "
$s \\cap s = s$ — intersection is **idempotent**.

The proof introduced two key notations:
- **`.1` and `.2`**: extract components from a conjunction hypothesis.
  If `h : P ∧ Q`, then `h.1 : P` and `h.2 : Q`.
- **`⟨a, b⟩`**: build a conjunction in one line. `⟨hs, hs⟩` builds
  `x ∈ s ∧ x ∈ s` by using the same proof twice.

You already know `constructor` splits a conjunction goal into two
subgoals. The anonymous constructor `⟨a, b⟩` is a one-line alternative
when both components are short.

This was the simplest `ext` identity: the logic reduced to
$P \\land P \\iff P$. Next you'll see identities where the logic is
more interesting.
"

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto
DisabledTheorem Finset.mem_insert_self Finset.mem_insert_of_mem Finset.mem_union_left Finset.mem_union_right Finset.mem_inter_of_mem Finset.mem_of_mem_inter_left Finset.mem_of_mem_inter_right Finset.subset_union_left Finset.subset_union_right Finset.inter_subset_left Finset.inter_subset_right Finset.union_comm Finset.inter_comm sup_comm inf_comm inf_le_left inf_le_right le_sup_left le_sup_right Finset.inter_self Finset.union_self inf_idem sup_idem Finset.union_empty Finset.empty_union sup_bot_eq bot_sup_eq and_self
