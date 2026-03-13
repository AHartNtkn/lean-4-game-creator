import Game.Metadata

World "SubgroupDef"
Level 6

Title "Introducing Hypotheses"

Introduction
"
When you *build* a subgroup, you'll need to prove statements like:

`∀ (a : G), a ∈ H → a⁻¹ ∈ H`

This says: *for every* `a` in `G`, *if* `a` belongs to `H`, *then*
`a⁻¹` belongs to `H`.

The `intro` tactic peels off universal quantifiers (`∀`) and
implications (`→`) from the goal, turning them into hypotheses in
your context.

For example, if the goal is `∀ (a : G), a ∈ H → a⁻¹ ∈ H`, writing
`intro a ha` gives you:
- `a : G` — a group element
- `ha : a ∈ H` — the assumption that `a` is in `H`

and the goal becomes `a⁻¹ ∈ H`.

Prove that every element of `H` has its inverse in `H`.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) :
    ∀ (a : G), a ∈ H → a⁻¹ ∈ H := by
  Hint "The goal is `∀ (a : G), a ∈ H → a⁻¹ ∈ H`. This has a
  universal quantifier (`∀`) and an implication (`→`).

  Use `intro a ha` to introduce both at once. This gives you
  `a : G` and `ha : a ∈ H`, and the goal becomes `a⁻¹ ∈ H`."
  intro a ha
  Hint "The goal is `a⁻¹ ∈ H` and you have `ha : a ∈ H`.

  This is exactly what `inv_mem` does. Try `exact inv_mem ha`."
  exact inv_mem ha

Conclusion
"
The `intro` tactic is how you work with `∀` and `→` in goals. You'll
use it constantly when building subgroups, because the closure
obligations all start with universal quantifiers and implications:

- `one_mem'`: no `intro` needed (just `1 ∈ carrier`)
- `mul_mem'`: `intro x y hx hy`
- `inv_mem'`: `intro x hx`

In the next level, you'll build your first subgroup from scratch,
using `intro` together with `refine` and `show`.
"
