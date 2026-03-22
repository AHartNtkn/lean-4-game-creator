import Game.Metadata

World "Powerset"
Level 4

Title "Subsets Live in the Powerset"

Introduction "
# Subset → Powerset Membership

If you already know that `s ⊆ t`, you can immediately conclude
that `s` is in the powerset of `t`.

**Your task**: Given `h : s ⊆ t`, prove `s ∈ t.powerset`.

The strategy is the same as Level 1: rewrite with `mem_powerset`,
then use your hypothesis.
"

/-- If s ⊆ t, then s ∈ t.powerset. -/
Statement (s t : Finset ℕ) (h : s ⊆ t) : s ∈ t.powerset := by
  Hint "The goal is `s ∈ t.powerset`. Convert this to a subset claim
  with `Finset.mem_powerset`."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset]`."
  rw [Finset.mem_powerset]
  Hint "The goal is now `s ⊆ t`, which is exactly your hypothesis `h`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
Two steps: `rw [Finset.mem_powerset]` then `exact h`.

The `mem_powerset` lemma is an iff (`↔`), and `rw` with an iff
replaces the left side with the right side in the goal. So
`rw [Finset.mem_powerset]` turns `s ∈ t.powerset` into `s ⊆ t`.

This is the **forward direction** of `mem_powerset`: from a subset
fact to a powerset membership fact. Next you'll practice the reverse
direction.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self
