import Game.Metadata

World "SubgroupBasics"
Level 4

Title "The Trivial Subgroup Is Smallest"

Introduction
"
You've shown `H ≤ ⊤` — every subgroup sits below `⊤`. Now prove
the other half: `⊥ ≤ H` — the trivial subgroup sits below everything.

The proof unfolds `⊥ ≤ H` to `∀ x, x ∈ ⊥ → x ∈ H`. Given
`x ∈ ⊥`, you know `x = 1` (by `Subgroup.mem_bot`). Once you
rewrite with this, the goal becomes `1 ∈ H`, which is `one_mem H`.
"

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] (H : Subgroup G) : ⊥ ≤ H := by
  Hint "The goal `⊥ ≤ H` means `∀ x, x ∈ ⊥ → x ∈ H`. Start with
  `intro x hx`."
  intro x hx
  Hint "You have `hx : {x} ∈ ⊥`. Use `rw [Subgroup.mem_bot] at hx`
  to learn that `{x} = 1`."
  rw [Subgroup.mem_bot] at hx
  Hint "Now `hx : {x} = 1`. Rewrite the goal with `rw [hx]` to
  change it to `1 ∈ H`, then close with `exact one_mem H`."
  rw [hx]
  exact one_mem H

Conclusion
"
Together with the previous level, you now have the full lattice
skeleton: for any subgroup `H`,

`⊥ ≤ H ≤ ⊤`

The trivial subgroup `{1}` is the bottom, and the whole group is
the top. Every subgroup sits between them.

The next operation in the lattice is **intersection**: given two
subgroups, their meet `H ⊓ K` is the largest subgroup contained
in both.
"
