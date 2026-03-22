import Game.Metadata

World "Powerset"
Level 5

Title "Powerset Membership → Subset"

Introduction "
# Reading a Powerset Membership

In Level 4, you went from a subset fact to powerset membership.
Now go the other direction: given that `s` is in the powerset of
`t`, extract the subset fact.

**Your task**: Given `h : s ∈ t.powerset`, prove `s ⊆ t`.

This time, the powerset fact is in a **hypothesis**, not the goal.
You'll use `rw [...] at h` to rewrite inside a hypothesis.
"

/-- If s ∈ t.powerset, then s ⊆ t. -/
Statement (s t : Finset ℕ) (h : s ∈ t.powerset) : s ⊆ t := by
  Hint "The hypothesis `h : s ∈ t.powerset` contains a subset fact
  in disguise. Use `rw [Finset.mem_powerset] at h` to unwrap it."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at h`."
  rw [Finset.mem_powerset] at h
  Hint "Now `h : s ⊆ t`, which is exactly the goal."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Two steps: `rw [Finset.mem_powerset] at h` then `exact h`.

The `at h` suffix tells `rw` to rewrite inside the hypothesis `h`
rather than in the goal. This is the **reverse direction** of
`mem_powerset`: extracting a subset fact from powerset membership.

**Pattern summary**:
- Goal contains `∈ powerset`: use `rw [mem_powerset]` (Level 4)
- Hypothesis contains `∈ powerset`: use `rw [mem_powerset] at h` (this level)

In ordinary math: saying '$s$ is in the powerset of $t$' and
saying '$s \\subseteq t$' are the same thing. `mem_powerset` is
the formal bridge between these two phrasings.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
