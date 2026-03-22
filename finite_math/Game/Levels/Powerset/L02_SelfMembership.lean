import Game.Metadata

World "Powerset"
Level 2

Title "Every Set Is in Its Own Powerset"

Introduction "
# Self-Membership

Level 1 showed that the empty set is always in the powerset.
The other natural endpoint is the set itself: every set `s`
is a member of its own powerset, because `s ⊆ s`.

**Your task**: Prove `s ∈ s.powerset`.

Strategy: rewrite powerset membership into a subset claim
(as in Level 1). This time, the subset claim `s ⊆ s` is
reflexively true — Lean closes it automatically.
"

/-- Every finset is a member of its own powerset. -/
Statement (s : Finset ℕ) : s ∈ s.powerset := by
  Hint "The goal is `s ∈ s.powerset`. Convert this to a subset claim
  using `Finset.mem_powerset`, just like in Level 1.
  Since `s ⊆ s` is reflexively true, the rewrite closes the goal."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset]`."
  rw [Finset.mem_powerset]

Conclusion "
One step: `rw [Finset.mem_powerset]`.

After rewriting, the goal becomes `s ⊆ s`, which Lean closes
automatically because subset is reflexive (`Finset.Subset.refl`).

The powerset always contains at least two distinguished members:
- `∅` (Level 1) — the empty set is a subset of everything
- `s` itself (this level) — every set is a subset of itself

These are the two extremes: the smallest and largest subsets.
Everything else in the powerset sits between them.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self
