import Game.Metadata

World "SubgroupDef"
Level 5

Title "Set-Builder Notation and `show`"

Introduction
"
To *build* a subgroup, you'll specify a **carrier set** — the set of
elements that belong to it. In Lean, sets are often written in
**set-builder notation**:

`{g : G | P g}`

This is the set of all `g` in `G` satisfying the predicate `P`.
For example, `{g : G | a * g = g * a}` is the set of all elements
that commute with `a`.

When your goal involves membership in such a set — say
`x ∈ {g : G | P g}` — it unfolds to `P x`. The tactic `show` lets
you explicitly replace the goal with this unfolded form:

`show P x`

This makes the goal concrete and easier to work with.

Prove that `1` is in the set `{g : G | a * g = g * a}` — the set
of elements that commute with `a`.

The `group` tactic could close this goal, but the point here is to
learn `show` — you'll need it when building subgroups, where `group`
won't help.
"

/-- The `show` tactic replaces the current goal with a definitionally
equal statement.

If the goal is `x ∈ {g : G | P g}`, you can write `show P x` to
unfold the set membership into the underlying predicate.

This is useful when the goal looks opaque (e.g., `x ∈ S`) and you
want to see what it *really* means.

`show` does not change the proof state — it only changes how the
goal is displayed. If the statement you provide is not definitionally
equal to the current goal, `show` will fail. -/
TacticDoc «show»

NewTactic «show»

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) :
    (1 : G) ∈ ({g : G | a * g = g * a} : Set G) := by
  Hint "The goal says `1` belongs to the set of elements commuting
  with `{a}`. This unfolds to `{a} * 1 = 1 * {a}`.

  Use `show {a} * 1 = 1 * {a}` to make this explicit, then close the
  goal with `rw`."
  show a * 1 = 1 * a
  Hint "Now the goal is `{a} * 1 = 1 * {a}`. Use `mul_one` and `one_mul`."
  rw [mul_one, one_mul]

Conclusion
"
The `show` tactic reveals what set membership *really means*. When
you see `x ∈ {g | P g}`, you can always `show P x` to get a concrete
mathematical goal.

You just proved that `1` commutes with `a` — this is the `one_mem'`
obligation for the centralizer subgroup. You'll use this in the boss.

This pattern is essential for building subgroups: when you define a
subgroup with carrier `{g | P g}`, the closure obligations become:

- `one_mem'`: `show P 1`
- `mul_mem'`: given `P x` and `P y`, `show P (x * y)`
- `inv_mem'`: given `P x`, `show P x⁻¹`

You'll see this pattern in action over the next few levels.
"
