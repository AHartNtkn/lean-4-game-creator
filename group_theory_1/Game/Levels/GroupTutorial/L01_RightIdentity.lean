import Game.Metadata

World "GroupTutorial"
Level 1

Title "Right Identity"

Introduction
"
Welcome to the Group Theory Game! In this first level, you'll meet the
basic notation for groups.

A **group** is a type `G` with a multiplication `*`, an identity element `1`,
and an inverse operation `⁻¹`. In Lean, if `a : G` where `G` is a group,
then `a * 1` means \"multiply `a` by the identity on the right\".

The theorem `mul_one` says that `a * 1 = a` — multiplying by the identity
on the right does nothing.

**Your task**: look at the goal and close it using `mul_one`.

You can either write `exact mul_one a` or `rw [mul_one]`.
"

/-- `rw [h]` rewrites the goal using an equation `h`. If `h : a = b`,
then `rw [h]` replaces `a` with `b` in the goal.

Use `rw [← h]` to rewrite in the reverse direction (replacing `b` with `a`).

You can chain rewrites: `rw [h₁, h₂, h₃]` applies them left to right. -/
TacticDoc rw

/-- `exact e` closes the goal if `e` has exactly the right type.

For example, if the goal is `a * 1 = a` and `mul_one a : a * 1 = a`,
then `exact mul_one a` closes the goal. -/
TacticDoc exact

/-- `mul_one` says `a * 1 = a` for any element `a` of a group.

Use it with `rw [mul_one]` when you see `_ * 1` in the goal, or with
`exact mul_one a` when the entire goal is `a * 1 = a`.

Don't confuse with `one_mul`, which handles `1 * a`. -/
TheoremDoc mul_one as "mul_one" in "Group"

/-- The `apply` tactic works **backwards** from the goal.

If the goal is `P` and you have `T : Q → P`, then `apply T` changes
the goal to `Q`.

More generally, if `T : A → B → C` and the goal is `C`, then
`apply T` creates two goals: `A` and `B`.

Think of it as: "to prove the goal, it suffices to prove `Q`,
because `T` turns `Q` into `P`." -/
TacticDoc apply

/-- The `intro` tactic introduces universally quantified variables
and hypotheses from the goal into the context.

If the goal is `∀ x : G, P x`, then `intro x` gives you
`x : G` and changes the goal to `P x`.

If the goal is `P → Q`, then `intro h` gives you `h : P` and
changes the goal to `Q`.

You can introduce multiple things at once: `intro x y h` introduces
`x`, `y`, and `h` in one step. -/
TacticDoc intro

/-- The `cases` tactic performs case analysis.

If `h : A ∨ B`, then `cases h` creates two goals — one assuming `A`
and one assuming `B`.

For inductive types, `cases` destructs into each constructor.

See also `obtain`, which lets you name the components directly. -/
TacticDoc cases

/-- The `constructor` tactic splits a goal that is a conjunction or
a structure with one constructor.

If the goal is `A ∧ B`, then `constructor` creates two goals:
one for `A` and one for `B`. -/
TacticDoc constructor

/-- The `assumption` tactic closes the goal if it exactly matches
one of the hypotheses in the context. -/
TacticDoc assumption

/-- The `have` tactic introduces an intermediate goal.

`have h : P := proof` adds `h : P` to the context.

`have h : P := by tac` lets you prove `P` with tactics first,
then adds it to the context for the rest of the proof.

Use `have` when you need to establish a fact before using it
in the main proof. -/
TacticDoc «have»

/-- The `use` tactic provides a witness for an existential goal.

If the goal is `∃ x, P x`, then `use a` changes the goal to `P a`.

**Example**: if the goal is `∃ x, f x = y`, then `use a` changes
it to `f a = y`. -/
TacticDoc use

NewTactic rw exact apply intro cases constructor assumption «have» use
NewTheorem mul_one

TheoremTab "Group"

Statement (G : Type*) [Group G] (a : G) : a * 1 = a := by
  Hint "Look at the goal: `a * 1 = a`. The `* 1` on the left side matches
  the pattern of `mul_one`. Try `rw [mul_one]` or `exact mul_one a`."
  Branch
    exact mul_one a
  rw [mul_one]

Conclusion
"
You just used `mul_one`, one of the five group axioms. In a group,
multiplying by the identity on the right does nothing.

Check your inventory — `mul_one` is now available for all future levels.
"
