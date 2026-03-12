import Game.Metadata

World "SubgroupBasics"
Level 2

Title "The Trivial Subgroup `⊥`"

Introduction
"
The symbol `⊥` (typed `\\bot`) denotes the **trivial subgroup** — the
smallest subgroup of any group `G`. Its only element is the identity
`1`.

The key lemma is `mem_bot`:

`Subgroup.mem_bot : x ∈ (⊥ : Subgroup G) ↔ x = 1`

**Warning**: `⊥` is `{1}`, not the empty set! A subgroup always
contains the identity, so the smallest possible subgroup is `{1}`.

You built this subgroup by hand in the previous world (Level 7, the
trivial subgroup `{g | g = 1}`). Now it has a name: `⊥`.

Given `a ∈ ⊥`, prove that `a = 1`.
"

/-- `Subgroup.mem_bot` characterizes membership in the trivial
subgroup `⊥`:

`Subgroup.mem_bot : x ∈ (⊥ : Subgroup G) ↔ x = 1`

To use it forward: `mem_bot.mp ha` converts `ha : a ∈ ⊥` to `a = 1`.
To rewrite: `rw [Subgroup.mem_bot] at ha` changes `ha : a ∈ ⊥` to
`ha : a = 1`.

Remember: `⊥` is `{1}`, not `∅`. The empty set is never a subgroup
because subgroups must contain `1`. -/
TheoremDoc Subgroup.mem_bot as "Subgroup.mem_bot" in "Subgroup"

NewTheorem Subgroup.mem_bot

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (a : G) (ha : a ∈ (⊥ : Subgroup G)) :
    a = 1 := by
  Hint "You have `ha : a ∈ ⊥` and need `a = 1`. The theorem
  `Subgroup.mem_bot` says `x ∈ ⊥ ↔ x = 1`.

  You can use `rw [Subgroup.mem_bot] at ha` to change `ha` to `a = 1`,
  then `exact ha`.

  Or in one step: `exact Subgroup.mem_bot.mp ha`."
  exact Subgroup.mem_bot.mp ha

Conclusion
"
The trivial subgroup `⊥` contains only the identity. This is the
bottom of the subgroup lattice — there's no subgroup smaller than
`{1}`.

The `.mp` in `Subgroup.mem_bot.mp` extracts the forward direction of
the `↔`. You could also use `rw [Subgroup.mem_bot] at ha` to rewrite
the hypothesis in place.

In Level 7 of the previous world, you built `{g | g = 1}` as a
`Subgroup G` by hand. That subgroup is exactly `⊥`.
"
