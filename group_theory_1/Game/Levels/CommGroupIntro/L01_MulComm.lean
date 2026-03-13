import Game.Metadata

World "CommGroupIntro"
Level 1

Title "Commutativity"

Introduction
"
Until now, every group `G` in this game has been a general `Group G`.
The order of multiplication mattered: `a * b` and `b * a` could be
different things.

A **commutative group** (or **abelian group**) is a group where
the order doesn't matter: `a * b = b * a` for all `a` and `b`.
In Lean, this is captured by the typeclass `CommGroup G`.

The theorem `mul_comm` states: for any `a b : G` where `G` is a
`CommGroup`, we have `a * b = b * a`.

Prove that `a * b = b * a`.
"

/-- `mul_comm` says `a * b = b * a` in any commutative group
(or commutative monoid/semigroup).

Use it with `rw [mul_comm]` when you need to swap two adjacent
factors, or `rw [mul_comm a b]` to target a specific pair. Without
arguments, `rw [mul_comm]` swaps the first `_ * _` it finds.

**Warning**: In a non-commutative group, this theorem is not
available. It requires `CommGroup` (or `CommMonoid`). -/
TheoremDoc mul_comm as "mul_comm" in "Group"

NewTheorem mul_comm

TheoremTab "Group"

Statement (G : Type*) [CommGroup G] (a b : G) : a * b = b * a := by
  Hint "The goal is `a * b = b * a`. The theorem `mul_comm` says
  exactly this. Try `exact mul_comm a b` or `rw [mul_comm]`."
  Branch
    exact mul_comm a b
  rw [mul_comm]

Conclusion
"
You've met `mul_comm`, the defining property of a commutative group.

Notice the type signature: we wrote `[CommGroup G]` instead of
`[Group G]`. This tells Lean that `G` is commutative, which makes
`mul_comm` available. If you tried to use `mul_comm` with only
`[Group G]`, Lean would refuse — it doesn't know the group is
commutative.

Remember the shoes-and-socks lemma from Group Basics:
`(a * b)⁻¹ = b⁻¹ * a⁻¹`, where the order *reversed*. With
`mul_comm`, you could rearrange that back to `a⁻¹ * b⁻¹` — no
reversal needed. That's the connection the earlier world promised.

In a `CommGroup`, you can freely rearrange the order of factors.
But *which* factors you swap matters when there are more than two.
In the next level, you'll learn to direct `mul_comm` at specific
pairs.
"
