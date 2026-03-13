import Game.Metadata

World "CenterIntro"
Level 2

Title "The Identity is Central"

Introduction
"
Is `1` in the center of every group? It should be — `1` commutes
with everything since `g * 1 = g = 1 * g`.

Prove this by unfolding center membership with `mem_center_iff`,
introducing the universal variable with `intro`, and then using
`mul_one` and `one_mul` to simplify.
"

TheoremTab "Center"

DisabledTactic group
DisabledTheorem OneMemClass.one_mem

Statement (G : Type*) [Group G] : (1 : G) ∈ Subgroup.center G := by
  Hint "Start with `rw [Subgroup.mem_center_iff]` to unfold center
  membership."
  rw [Subgroup.mem_center_iff]
  Hint "The goal is `∀ (g : G), g * 1 = 1 * g`. Introduce the
  universal variable with `intro g`."
  intro g
  Hint "Now simplify: `rw [mul_one]` handles the left side,
  `rw [one_mul]` handles the right."
  Hint (hidden := true) "`rw [mul_one, one_mul]`"
  rw [mul_one, one_mul]

Conclusion
"
This is the `one_mem` part of the membership triple for the center.
On paper: *\"For any `g`, `g · 1 = g = 1 · g`, so `1` commutes with
everything.\"*

Notice the new wrinkle compared to the subgroup membership triple
from earlier worlds: here, after `rw [Subgroup.mem_center_iff]`,
you had to `intro g` to introduce the universal quantifier before
doing algebra. Every center membership proof follows this
**unfold-intro-algebra** pattern:

1. `rw [Subgroup.mem_center_iff]` — unfold
2. `intro g` — introduce the universal variable
3. algebraic steps — prove `g * z = z * g`

You'll use this pattern three more times in this world.
"
