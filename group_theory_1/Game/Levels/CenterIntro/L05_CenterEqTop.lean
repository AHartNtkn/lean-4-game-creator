import Game.Metadata

World "CenterIntro"
Level 5

Title "Abelian Groups Have Full Center"

Introduction
"
In a commutative group, every element commutes with everything.
So the center should be the entire group — `center G = ⊤`.

To show a subgroup equals `⊤`, use the lemma `Subgroup.eq_top_iff'`:

`H = ⊤ ↔ ∀ x, x ∈ H`

This reduces `center G = ⊤` to showing every element is in the center,
which follows from `mul_comm`.
"

/-- `Subgroup.eq_top_iff'` says:

`H = ⊤ ↔ ∀ x : G, x ∈ H`

To show a subgroup is the whole group, show every element is a member.

Use `rw [Subgroup.eq_top_iff']` to convert `H = ⊤` in the goal,
or `rw [Subgroup.eq_top_iff'] at h` to convert it in a hypothesis. -/
TheoremDoc Subgroup.eq_top_iff' as "Subgroup.eq_top_iff'" in "Subgroup"

NewTheorem Subgroup.eq_top_iff' CommGroup.center_eq_top

/-- `CommGroup.center_eq_top` says that in a commutative group, the
center is the whole group: `Subgroup.center G = ⊤`.

This is what you're proving in this level — it's disabled so you
prove it yourself. After completing the level, you'll have it as a
theorem you can use in future worlds. -/
TheoremDoc CommGroup.center_eq_top as "CommGroup.center_eq_top" in "Center"
DisabledTheorem CommGroup.center_eq_top

TheoremTab "Center"

DisabledTactic group

Statement (G : Type*) [CommGroup G] : Subgroup.center G = ⊤ := by
  Hint "To show a subgroup equals `⊤`, use
  `rw [Subgroup.eq_top_iff']` to reduce to showing every element
  is a member."
  rw [Subgroup.eq_top_iff']
  Hint "The goal is `∀ (x : G), x ∈ Subgroup.center G`. Introduce
  the element with `intro x`."
  intro x
  Hint "Now show `{x} ∈ Subgroup.center G`. Unfold with
  `rw [Subgroup.mem_center_iff]`."
  rw [Subgroup.mem_center_iff]
  Hint "The goal is `∀ (g : G), g * {x} = {x} * g`. Introduce `g`
  and use `mul_comm` from the `CommGroup` instance."
  intro y
  Hint (hidden := true) "`exact mul_comm y {x}`"
  exact mul_comm y x

Conclusion
"
In a commutative group, the center is everything — because every
element commutes with every other element by definition.

The new tool `Subgroup.eq_top_iff'` reduces `H = ⊤` to
`∀ x, x ∈ H`. It's the standard way to show a subgroup is the
whole group.

This is the forward direction of the characterization:
*abelian implies center = ⊤*. Next: the converse — if
`center G = ⊤`, then the group is abelian.

You'll then combine both directions with `refine ⟨?_, ?_⟩` in the
boss. This **split-and-recombine** pattern — prove each direction
of an `↔` separately, then assemble — is the standard approach
for all characterization theorems.
"
