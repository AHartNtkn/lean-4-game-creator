import Game.Metadata

World "SubgroupBasics"
Level 3

Title "Everything Is in `⊤`"

Introduction
"
The symbol `⊤` (typed `\\top`) denotes the **whole group** viewed as
a subgroup of itself. Every element of `G` belongs to `⊤`.

The key lemma is `mem_top`:

`Subgroup.mem_top (x : G) : x ∈ (⊤ : Subgroup G)`

Note that `mem_top` is not an `↔` — it's just a proof that `x ∈ ⊤`
for any `x`. Membership in `⊤` is always true.

In Level 10 of the previous world, you built `{g | True}` as a
subgroup. That subgroup is exactly `⊤`.

Prove that any subgroup `H` is contained in `⊤`.
"

/-- `Subgroup.mem_top` says that every element belongs to the
whole group `⊤`:

`Subgroup.mem_top (x : G) : x ∈ (⊤ : Subgroup G)`

Unlike `mem_bot`, this is not an `↔` — it's a direct proof of
membership. Use it as `exact Subgroup.mem_top x` when the goal is
`x ∈ ⊤`. -/
TheoremDoc Subgroup.mem_top as "Subgroup.mem_top" in "Subgroup"

NewTheorem Subgroup.mem_top

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) : H ≤ ⊤ := by
  Hint "The goal `H ≤ ⊤` unfolds to `∀ x, x ∈ H → x ∈ ⊤`. Use
  `intro x hx` to introduce a group element and its membership
  hypothesis, then show `x ∈ ⊤`."
  intro x hx
  Hint "The goal is `{x} ∈ ⊤`. Use `exact Subgroup.mem_top {x}`."
  exact Subgroup.mem_top x

Conclusion
"
Every subgroup is contained in `⊤`. But what about the other
direction — is every subgroup *above* `⊥`? That's the next level.
"
