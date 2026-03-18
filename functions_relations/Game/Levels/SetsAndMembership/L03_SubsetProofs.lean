import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 3

Title "Subset Proofs"

Introduction
"
A set `A` is a **subset** of `B`, written `A ⊆ B`, when every element
of `A` is also an element of `B`. In Lean, `A ⊆ B` unfolds to:

`∀ x, x ∈ A → x ∈ B`

That is: for every `x`, if `x` is in `A`, then `x` is in `B`.

Since this is a `∀` statement followed by an `→`, the standard approach
is: `intro x` to name the element, then `intro hx` to assume `x ∈ A`,
and finally prove `x ∈ B`.

In this level, you will prove that every set is a subset of itself.
This is the simplest possible subset proof, but it establishes the
fundamental pattern: **intro the element, intro the membership
hypothesis, then prove the goal**.

**New definitions**: `⊆` — subset relation on sets. `A ⊆ B` means
`∀ x, x ∈ A → x ∈ B`.

**Note**: Lean also has `⊂` (strict subset, meaning `A ⊆ B ∧ A ≠ B`),
but we will not use it in this course. When we write `⊆`, equality is
allowed — `A ⊆ A` is always true.
"

/-- `A ⊆ B` means that every element of `A` is also an element of `B`.
Formally, `A ⊆ B` is defined as `∀ x, x ∈ A → x ∈ B`.

To prove `A ⊆ B`, use `intro x hx` to assume `x ∈ A`, then show `x ∈ B`.
To *use* `h : A ⊆ B` with a specific element, use `h hx` where `hx : x ∈ A`
to get `x ∈ B`.

Note: `⊆` allows equality (like ≤). Lean also has `⊂` for strict subset
(like <), but we will not use it in this course. -/
DefinitionDoc HasSubset.Subset as "⊆"

/-- `x ∈ S` means that `x` is an element of the set `S`. For sets defined
as `\u007By | P y\u007D`, membership `x ∈ \u007By | P y\u007D` is definitionally
equal to `P x`. -/
DefinitionDoc Set.Mem as "∈ (sets)"

NewDefinition HasSubset.Subset Set.Mem

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem subset_refl Set.Subset.refl le_refl

Statement (A : Set ℕ) : A ⊆ A := by
  Hint "The goal is `A ⊆ A`, which means `∀ x, x ∈ A → x ∈ A`.
  Start by introducing the element: try `intro x`."
  intro x
  Hint "Now introduce the membership hypothesis: try `intro hx`."
  intro hx
  Hint "The goal is `x ∈ A` and you have `hx : x ∈ A`. These are the same!
  Use `exact hx` to close the goal."
  exact hx

Conclusion
"
You proved that every set is a subset of itself — the **reflexivity** of `⊆`.

The proof pattern for subset goals is always the same:

1. `intro x` — name an arbitrary element.
2. `intro hx` — assume it belongs to the left-hand set.
3. Prove it belongs to the right-hand set.

In this case, step 3 was trivial because both sets were the same. In
future levels, step 3 will require real work.
"
