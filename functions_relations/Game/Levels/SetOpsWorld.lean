import Game.Levels.SetOpsWorld.L01_UnionMembership
import Game.Levels.SetOpsWorld.L02_IntersectionMembership
import Game.Levels.SetOpsWorld.L03_ComplementMembership
import Game.Levels.SetOpsWorld.L04_SetDifference
import Game.Levels.SetOpsWorld.L05_DiffAsIntersect
import Game.Levels.SetOpsWorld.L06_IntersectionSubset
import Game.Levels.SetOpsWorld.L07_IntersectionCommutativity
import Game.Levels.SetOpsWorld.L08_UnionSubset
import Game.Levels.SetOpsWorld.L09_ComplementLaw
import Game.Levels.SetOpsWorld.L10_UnionCaseAnalysis
import Game.Levels.SetOpsWorld.L11_PushNeg
import Game.Levels.SetOpsWorld.L12_DeMorgan
import Game.Levels.SetOpsWorld.L13_DualDeMorgan
import Game.Levels.SetOpsWorld.L14_ComplementUnion
import Game.Levels.SetOpsWorld.L15_DoubleComplement
import Game.Levels.SetOpsWorld.L16_Boss

World "SetOpsWorld"
Title "Set Operations World"

Introduction "
# Set Operations World

In Set World, you learned that sets are predicates. In Subset World,
you learned to prove subset and equality relationships between sets.
Now you will learn the four fundamental **set operations** — and
discover that each one is a logical connective in disguise:

| Operation | Notation | Logical meaning |
|---|---|---|
| Union | `s ∪ t` | `x ∈ s ∨ x ∈ t` |
| Intersection | `s ∩ t` | `x ∈ s ∧ x ∈ t` |
| Complement | `sᶜ` | `¬ (x ∈ s)` |
| Difference | `s \\ t` | `x ∈ s ∧ x ∉ t` |

This correspondence is the deepest fact about sets in Lean: **every
set operation reduces to a propositional connective**. Set-theoretic
reasoning IS logical reasoning.

By the end of this world, you will be able to:
- Prove membership in unions, intersections, complements, and differences
- Prove subset relations involving these operations
- Perform case analysis on union hypotheses
- Use `push_neg` to simplify negated compound propositions
- Prove De Morgan's laws for sets (both directions)
- Use `by_contra` for proof by contradiction
- Prove the complement laws, double complement, and distributivity

**New tools in this world**:
- `left` / `right` — choose a side of a disjunction (or union)
- `push_neg` — push negation through logical connectives
- `by_contra` — proof by contradiction
- `cases h with | inl ... | inr ...` — case analysis on disjunctions
  (the `cases` tactic is familiar; what is new here are the constructor
  names `inl` and `inr` for the two branches of `Or`)

**Prerequisites**: Set World (membership, show/change) and Subset World
(intro x hx, ext, constructor, obtain).
"
