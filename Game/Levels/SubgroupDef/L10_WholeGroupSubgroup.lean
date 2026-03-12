import Game.Metadata

World "SubgroupDef"
Level 10

Title "Building the Whole Group"

Introduction
"
Before the boss, one more subgroup construction for practice.

In Level 7, you built the **trivial subgroup** `{1}` — the smallest
subgroup. Now build the opposite extreme: the **whole group** as a
subgroup of itself.

The carrier is the set of ALL elements — use the predicate `True`,
which every element satisfies. The closure proofs are trivially
easy — the tactic `trivial` closes goals like `True`.

Same pattern as Level 7: `apply Subgroup.mk_carrier`, then prove
each obligation.
"

/-- `trivial` closes simple goals like `True`, `1 = 1`, or anything
that follows from basic logic.

It is a Swiss-army-knife tactic for trivially true goals. When the
goal is `True`, `trivial` closes it immediately. -/
TacticDoc trivial

/-- `True` is a proposition that is always true. The tactic `trivial`
proves it.

In set-builder notation, `{g : G | True}` is the set of ALL elements
of `G`, since every element satisfies `True`. -/
DefinitionDoc True as "True"

NewTactic trivial
NewDefinition True

TheoremTab "Subgroup"

Statement (G : Type*) [Group G] :
    ∃ H : Subgroup G, H.carrier = {g : G | True} := by
  Hint "Same pattern as Level 7: `apply Subgroup.mk_carrier`."
  apply Subgroup.mk_carrier
  · Hint "**mul_mem**: If two elements satisfy `True`, their product
    does too.

    `intro x y _ _` to introduce and discard the trivial hypotheses,
    then `trivial`."
    Hint (hidden := true) "`intro x y _ _` then `trivial`"
    intro x y _ _
    trivial
  · Hint "**one_mem**: Show `1` satisfies `True`.

    `trivial` closes this immediately."
    trivial
  · Hint "**inv_mem**: If an element satisfies `True`, its inverse
    does too.

    `intro x _` then `trivial`."
    intro x _
    trivial

Conclusion
"
The whole group is a subgroup of itself — the largest possible
subgroup. In Lean, this is called `⊤` (\"top\").

The math was trivial here, but the pattern was the same:

1. `apply Subgroup.mk_carrier` — creates three obligations
2. For each obligation: `intro` the hypotheses, then prove the claim.

You've now built two subgroups: the trivial subgroup (the smallest)
and the whole group (the largest). In the boss, you'll build one
where the closure proofs require real algebra: the centralizer.
"
