import Game.Metadata

World "Powerset"
Level 24

Title "Subsets Can't Be Bigger"

Introduction "
# Subset Cardinality Bound

If `t` is in the powerset of `s`, then `t` is a subset of `s`,
so `t` can't have more elements than `s`. This is the bound:

$$t \\in \\mathcal{P}(s) \\implies |t| \\leq |s|$$

This combines two things you know:
- `mem_powerset` to extract `t ⊆ s`
- `Finset.card_le_card` (from the Cardinality world) to conclude
  `t.card ≤ s.card`

**Your task**: Given `ht : t ∈ s.powerset`, prove `t.card ≤ s.card`.
"

/-- A member of the powerset has bounded cardinality. -/
Statement (s t : Finset ℕ) (ht : t ∈ s.powerset) :
    t.card ≤ s.card := by
  Hint "First, extract the subset fact from `ht` using `mem_powerset`."
  Hint (hidden := true) "Try `rw [Finset.mem_powerset] at ht`."
  rw [Finset.mem_powerset] at ht
  Hint "Now `ht : t ⊆ s`. From the Cardinality world, you know that
  subsets can't be bigger: `Finset.card_le_card` says `t ⊆ s → t.card ≤ s.card`."
  Hint (hidden := true) "Try `exact Finset.card_le_card ht`."
  exact Finset.card_le_card ht

Conclusion "
Two steps:
1. `rw [mem_powerset] at ht` — extract `t ⊆ s`
2. `exact card_le_card ht` — conclude `t.card ≤ s.card`

This level integrates the powerset world with the Cardinality world.
The `mem_powerset` bridge converts a powerset fact into a subset fact,
which `card_le_card` can use.

**Proof pattern**: When you need a cardinality inequality from a
powerset membership, the recipe is always:
1. Extract the subset with `mem_powerset`
2. Apply the cardinality lemma

This pattern will recur whenever powerset arguments interact with
counting.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto linarith nlinarith
DisabledTheorem Finset.empty_mem_powerset Finset.mem_powerset_self Finset.powerset_mono
