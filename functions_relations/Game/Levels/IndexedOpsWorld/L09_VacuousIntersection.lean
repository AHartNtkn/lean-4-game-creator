import Game.Levels.IndexedOpsWorld.Imports

World "IndexedOpsWorld"
Level 9

Title "Vacuous Intersection"

Introduction "
# When the Index Type Is Empty

What happens when you take the intersection over an *empty* family of
sets? If the index type has no elements at all, then `⋂ i, s i` should
contain everything — because the condition `∀ i, x ∈ s i` is
**vacuously true** when there are no indices to check.

This is one of the most surprising properties of indexed intersections.
When you intersect over nothing, you get everything:

$$\\bigcap_{i \\in \\emptyset} s_i = \\text{univ}$$

Students often picture intersections as always \"shrinking\" a collection.
But when there are no constraints, there is nothing to shrink — every
element satisfies all zero conditions.

This is also why **bounded** variants (`⋂ i ∈ t, s i`) exist: they let
you restrict to a non-vacuous index set, avoiding this surprise.

**Your task**: Prove that the intersection over the empty index type
is `Set.univ`.
"

NewTheorem Set.mem_iUnion Set.mem_iInter Set.mem_iUnion₂ Set.mem_iInter₂
NewDefinition Set.iUnion Set.iInter Empty
TheoremTab "Set"

/-- The intersection over an empty index type is the universal set. -/
Statement (α : Type) (s : Empty → Set α) :
    ⋂ i, s i = Set.univ := by
  Hint "This is a set equality. Start with `ext x` to reduce to a
  membership biconditional."
  ext x
  Hint "Use `constructor` to split the `↔`."
  constructor
  · Hint "The forward direction is trivial: everything is in `Set.univ`.
    Use `intro _` then `exact Set.mem_univ x`."
    Hint (hidden := true) "`intro _` then `exact Set.mem_univ x`."
    intro _
    exact Set.mem_univ x
  · Hint "The backward direction is the interesting one. You need to show
    `x ∈ ⋂ i, s i`. Use `intro _` to dismiss the trivial hypothesis,
    then `rw [Set.mem_iInter]` to convert the goal to `∀ i, x ∈ s i`."
    intro _
    Hint "Use `rw [Set.mem_iInter]` to convert to a universal."
    rw [Set.mem_iInter]
    Hint "The goal is `∀ (i : Empty), x ∈ s i`. Since `Empty` has no
    elements, you need to handle every element of `Empty` — but there
    are none! Use `intro i` to introduce a hypothetical index, then
    `exact i.elim` to eliminate the impossible case.

    `Empty.elim` says: if you have an element of `Empty`, you can prove
    anything — because such an element cannot exist."
    Hint (hidden := true) "`intro i` then `exact i.elim` — an element of
    `Empty` can prove anything, because it cannot exist."
    intro i
    exact i.elim

Conclusion "
You proved that `⋂ i : Empty, s i = Set.univ` — intersecting over
an empty index gives everything.

The key insight is **vacuous truth**: the statement `∀ i : Empty, P i`
is true because there are no `i` to check. In Lean, `Empty` is a type
with no constructors, so `i.elim` (equivalently, `Empty.elim i`)
discharges any goal about an element of `Empty`.

**`Empty.elim` and `False.elim`**: The pattern `i.elim` for `i : Empty`
is the type-level version of `False.elim` for `h : False`. Both say
\"from an impossible premise, anything follows\" — the principle of
explosion. You will see `False.elim` in propositional logic and
`Empty.elim` when working with uninhabited types (like `Fin 0`).

**Why this matters**: This explains why **bounded** indexed intersections
(`⋂ i ∈ t, s i`) are needed. If `t` might be empty, the bounded
intersection degenerates to `Set.univ`, which is often not what you
want. When you see a bounded intersection in a proof, always consider:
what happens if the bounding set is empty?

**Up next**: You will prove the dual — `⋃ i : Empty, s i = ∅` —
completing the most dramatic duality pair in this world.

In ordinary math: \"The intersection $\\bigcap_{i \\in \\emptyset} s_i$
contains every element, because the defining condition — $x \\in s_i$
for all $i \\in \\emptyset$ — is vacuously satisfied.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num linarith
DisabledTheorem Set.mem_setOf_eq Set.mem_setOf Set.iInter_of_empty iInter_of_empty
