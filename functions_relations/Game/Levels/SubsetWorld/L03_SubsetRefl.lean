import Game.Metadata

World "SubsetWorld"
Level 3

Title "Subset Reflexivity"

Introduction "
# Every Set Is a Subset of Itself

Before exploring boundary cases (`∅` and `Set.univ`), let us prove
the simplest subset fact: every set is a subset of itself.

$$s \\subseteq s$$

This is **reflexivity** of `⊆`. The proof is the simplest possible
`⊆` proof: after `intro x hx`, the goal is `x ∈ s` and you already
have `hx : x ∈ s`. The hypothesis IS the goal.

**Proof plan**:
1. `intro x hx` — assume `x ∈ s`
2. `exact hx` — the hypothesis is exactly the goal
"

/-- Every set is a subset of itself. -/
Statement (α : Type) (s : Set α) : s ⊆ s := by
  Hint "Use `intro x hx` to introduce the element and the membership
  assumption, just as in Level 1."
  intro x hx
  Hint "The goal is `x ∈ s` and you have `hx : x ∈ s`. The hypothesis
  matches the goal exactly — use `exact hx`."
  exact hx

Conclusion "
The proof of `s ⊆ s` is the identity function on membership: take the
proof that `x ∈ s` and hand it right back.

This is **reflexivity**: `s ⊆ s` for every `s`. Together with
transitivity (coming in Level 8) and antisymmetry (Level 13), this
makes `⊆` a **partial order** on sets. You will prove all three
axioms in this world.

The library name for this fact is `Set.Subset.refl` (or `le_refl`
in the order-theoretic form).
"

/-- `Set.Subset.refl s` proves `s ⊆ s` (subset reflexivity). -/
TheoremDoc Set.Subset.refl as "Set.Subset.refl" in "Set"

NewTheorem Set.Subset.refl

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.Subset.refl le_refl Preorder.le_refl Set.Subset.rfl le_rfl le_of_eq Eq.le Eq.subset Set.mem_setOf_eq Set.mem_setOf
