import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 13

Title "Double Inclusion"

Introduction
"
There is a second way to prove two sets are equal: **double inclusion**.
If `A ⊆ B` and `B ⊆ A`, then `A = B`. This is the theorem
`Set.Subset.antisymm`.

This approach is sometimes more natural than `ext` because you can
prove each inclusion separately, using the familiar subset pattern
(`intro x hx`, then chase membership).

The `apply` tactic works well here: `apply Set.Subset.antisymm` will
split the equality goal `A = B` into two subgoals: `A ⊆ B` and `B ⊆ A`.

In this level, `ext` is disabled so you must use double inclusion.

**New theorem**: `Set.Subset.antisymm` — if `A ⊆ B` and `B ⊆ A` then `A = B`.
"

/-- `Set.Subset.antisymm` states that subset is antisymmetric: if `A ⊆ B` and
`B ⊆ A`, then `A = B`. This gives a second way to prove set equality
(the first being `ext`).

## Statement
`Set.Subset.antisymm : A ⊆ B → B ⊆ A → A = B`

## When to use
Use this when proving `A = B` by showing inclusion in both directions.
After `apply Set.Subset.antisymm`, you get two subgoals: `A ⊆ B` and `B ⊆ A`. -/
TheoremDoc Set.Subset.antisymm as "Set.Subset.antisymm" in "Set"

NewTheorem Set.Subset.antisymm

TheoremTab "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num ext

Statement (P Q : ℕ → Prop) (h : ∀ x, P x ↔ Q x) :
    ({x : ℕ | P x} : Set ℕ) = {x : ℕ | Q x} := by
  Hint "The goal is set equality. This time, `ext` is disabled, so use
  double inclusion instead. Try `apply Set.Subset.antisymm` to split
  the goal into two subset goals."
  apply Set.Subset.antisymm
  · Hint "First subgoal: show the first set is a subset of the second.
    Start with `intro x hx`."
    intro x hx
    Hint "You have `hx : P x` (after unfolding set membership) and need
    `Q x`. The hypothesis `h` gives you `P x ↔ Q x` for all `x`.
    Try `exact (h x).mp hx`."
    exact (h x).mp hx
  · Hint "Second subgoal: show the reverse inclusion. Same pattern,
    using `.mpr` instead of `.mp`."
    intro x hx
    exact (h x).mpr hx

Conclusion
"
You proved set equality by double inclusion using `Set.Subset.antisymm`.

**Two approaches to set equality**:

1. **`ext`**: Reduces `A = B` to `∀ x, x ∈ A ↔ x ∈ B`, then you
   prove the iff for each element.

2. **`Set.Subset.antisymm`**: Reduces `A = B` to `A ⊆ B` and `B ⊆ A`,
   then you prove each inclusion separately.

Both approaches are correct. `ext` is more direct when the equivalence
is pointwise obvious. Double inclusion is more natural when the two
directions have different proof structures.

The boss level will ask you to combine everything you have learned.
"
