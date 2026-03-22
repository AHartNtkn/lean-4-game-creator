import Game.Levels.FinsetOperations.L01_UnionMembership
import Game.Levels.FinsetOperations.L02_IntersectionMembership
import Game.Levels.FinsetOperations.L03_SetDifference
import Game.Levels.FinsetOperations.L04_FilterByPredicate
import Game.Levels.FinsetOperations.L05_Subset
import Game.Levels.FinsetOperations.L06_SubsetMonotonicity
import Game.Levels.FinsetOperations.L07_EqualityByAntisymmetry
import Game.Levels.FinsetOperations.L08_Extensionality
import Game.Levels.FinsetOperations.L09_IntersectionIdempotency
import Game.Levels.FinsetOperations.L10_EmptySetIdentity
import Game.Levels.FinsetOperations.L11_DisjointFinsets
import Game.Levels.FinsetOperations.L12_Idempotency
import Game.Levels.FinsetOperations.L13_IntersectionCommutativity
import Game.Levels.FinsetOperations.L14_UnionCommutativity
import Game.Levels.FinsetOperations.L15_UnionAssociativity
import Game.Levels.FinsetOperations.L16_LatticeNotation
import Game.Levels.FinsetOperations.L17_TargetedSimplification
import Game.Levels.FinsetOperations.L18_DeMorgansLaw
import Game.Levels.FinsetOperations.L19_ProofByContradiction
import Game.Levels.FinsetOperations.L20_ComplementViaSdiff
import Game.Levels.FinsetOperations.L21_PartitionIdentity
import Game.Levels.FinsetOperations.L22_AbsorptionLaw
import Game.Levels.FinsetOperations.L23_Distributivity
import Game.Levels.FinsetOperations.L24_DualDistributivity
import Game.Levels.FinsetOperations.L25_Boss

World "FinsetOperations"
Title "Finset Operations"

Introduction "
# Finset Operations: Union, Intersection, and Equality

You know how to build finsets and prove membership. But mathematics needs
more than just 'is this element in the set?' — it needs *operations*:
union, intersection, set difference, and filtering.

The key insight of this world: **every finset operation has a membership
characterization**. Instead of reasoning about the operations directly,
you unwrap them into membership statements using characterization lemmas:

- **Union**: `x ∈ s ∪ t ↔ x ∈ s ∨ x ∈ t`
- **Intersection**: `x ∈ s ∩ t ↔ x ∈ s ∧ x ∈ t`
- **Difference**: `x ∈ s \\ t ↔ x ∈ s ∧ x ∉ t`
- **Filter**: `x ∈ s.filter p ↔ x ∈ s ∧ p x`

Once you've unwrapped the operation, the goal becomes pure logic — `∨`,
`∧`, `¬` — which you already know how to handle.

You'll also learn two ways to prove that two finsets are **equal**:
1. **Mutual containment**: show `s ⊆ t` and `t ⊆ s` (valid but verbose)
2. **Extensionality**: show `∀ x, x ∈ s ↔ x ∈ t` using the `ext` tactic (the standard approach)

The `ext` tactic is especially powerful: it converts a set equality into
a universal membership equivalence, letting you work element-by-element.
Combined with `simp only` for targeted membership unfolding, this gives
you a clean proof recipe for any set identity:

1. `ext x` — reduce to element-wise logic
2. `simp only [mem_union, mem_inter, ...]` — unfold all operations
3. Handle the resulting ∧/∨/¬ with `constructor`, `cases`, `left`/`right`

**Note on `ext`**: You know `ext` from MeetFin, but it's temporarily
disabled in Levels 1-7. Those levels focus on the individual membership
characterization lemmas — the building blocks that `ext` proofs are
built from. `ext` returns at Level 8, where you'll learn to use it
specifically for Finset extensionality.

**About this world's length**: This is a substantial world (25 levels)
covering membership lemmas, subset/equality, set identities (idempotency,
commutativity, associativity, absorption, distributivity), and De Morgan's
laws. Each level teaches one distinct identity or technique. If you find
the middle section (identity proofs) becoming routine, that's a sign you've
internalized the recipe — which is exactly the point. The boss at the
end combines set difference with the unfold-to-logic recipe.
"
