import Game.Metadata

World "CenterIntro"
Level 1

Title "Center Membership"

Introduction
"
The **center** of a group `G` is the subgroup of all elements that
commute with every other element:

`center G = {z : G | ∀ g : G, g * z = z * g}`

In Lean, this is `Subgroup.center G`. The key lemma for working with
the center is `Subgroup.mem_center_iff`:

`z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g`

This converts between the abstract \"membership in center\" and the
concrete \"commutes with everything\" condition. Almost every proof
about the center starts with `rw [Subgroup.mem_center_iff]`.

Given an element `z` that commutes with everything, show it's in the
center.
"

/-- The center of a group `G`, written `Subgroup.center G`, is the
subgroup of elements that commute with everything:

`center G = {z : G | ∀ g : G, g * z = z * g}`

Use `Subgroup.mem_center_iff` to convert between membership and the
commuting condition. -/
DefinitionDoc Subgroup.center as "Subgroup.center"

NewDefinition Subgroup.center

/-- `Subgroup.mem_center_iff` says:

`z ∈ Subgroup.center G ↔ ∀ g, g * z = z * g`

Use `rw [Subgroup.mem_center_iff]` to unfold center membership
in the goal, or `rw [Subgroup.mem_center_iff] at h` to unfold
it in a hypothesis.

Example: if the goal is `z ∈ Subgroup.center G`, then
`rw [Subgroup.mem_center_iff]` changes it to `∀ g, g * z = z * g`. -/
TheoremDoc Subgroup.mem_center_iff as "Subgroup.mem_center_iff" in "Center"

NewTheorem Subgroup.mem_center_iff

TheoremTab "Center"

DisabledTactic group

Statement (G : Type*) [Group G] (z : G) (hz : ∀ g : G, g * z = z * g) :
    z ∈ Subgroup.center G := by
  Hint "Use `rw [Subgroup.mem_center_iff]` to convert the goal from
  `{z} ∈ Subgroup.center G` to `∀ g, g * {z} = {z} * g`."
  rw [Subgroup.mem_center_iff]
  Hint (hidden := true) "The goal is now `∀ (g : G), g * {z} = {z} * g`,
  which is exactly `hz`. Use `exact hz`."
  exact hz

Conclusion
"
The lemma `Subgroup.mem_center_iff` is the gateway to all center
reasoning. It converts between the abstract membership `z ∈ center G`
and the concrete condition `∀ g, g * z = z * g`.

Notice the direction of the commuting condition: `g * z = z * g`
where the universal variable `g` is on the *left* of the product.
This is Mathlib's convention.

Next: you'll prove that `1` is always in the center — the first
part of showing that the center is a subgroup.
"
