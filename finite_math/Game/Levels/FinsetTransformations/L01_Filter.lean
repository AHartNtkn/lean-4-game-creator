import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 1

Title "Filtering a finset"

Introduction
"
# Filtering a finset by a predicate

In the previous world you learned to combine finsets using union,
intersection, and difference. Now we turn to **transformations** that
build new finsets from old ones by testing or modifying elements.

## `Finset.filter`

Given a finset `s` and a predicate `p`, the expression
`Finset.filter p s` (or equivalently `{x ∈ s | p x}`) returns the
finset of elements of `s` that satisfy `p`.

The key membership lemma is:

```
Finset.mem_filter : a ∈ s.filter p ↔ a ∈ s ∧ p a
```

An element belongs to the filtered finset exactly when it belongs to
the original finset **and** satisfies the predicate.

## `DecidablePred`

Filtering requires a `DecidablePred p` instance -- Lean must be able
to compute `p a` for each element. For predicates built from numeric
comparisons, `Nat.decEq`, `Nat.decLe`, etc., Lean can infer this
automatically.

## Your task

Prove that `2` belongs to the finset obtained by filtering
{1, 2, 3, 4, 5} with the predicate \"is even\" (i.e., `x % 2 = 0`).

**Strategy**: Rewrite with `Finset.mem_filter` to split the goal into
a conjunction, then prove each part.
"

/-- `2` belongs to the even elements of `{1, 2, 3, 4, 5}`. -/
Statement : (2 : Nat) ∈ Finset.filter (fun x => x % 2 = 0) {1, 2, 3, 4, 5} := by
  Hint "The goal asks whether `2` is in the filtered finset. Use
  `Finset.mem_filter` to split this into two parts: membership in the
  original finset and the predicate `2 % 2 = 0`."
  Hint (hidden := true) "Use `rw [Finset.mem_filter]`."
  rw [Finset.mem_filter]
  Hint "The goal is now a conjunction. Use `constructor` to split it
  into two subgoals."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "Prove that `2` belongs to the original finset. You know how
    to do this from the Membership world."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Prove that `2 % 2 = 0`. This is a numeric computation."
    Hint (hidden := true) "Use `rfl` or `norm_num`."
    rfl

Conclusion
"
You proved your first filter membership fact. The proof had two parts:

1. **Membership in the original finset**: `2 ∈ {1, 2, 3, 4, 5}`.
2. **The predicate holds**: `2 % 2 = 0`.

The key lemma `Finset.mem_filter` turns every filter membership goal
into a conjunction of these two obligations. This pattern will appear
throughout the world.

**Notation**: You can also write the filtered finset as
`{x ∈ {1, 2, 3, 4, 5} | x % 2 = 0}`. This is notation for
`Finset.filter (fun x => x % 2 = 0) {1, 2, 3, 4, 5}`.
"

/-- `Finset.mem_filter` states that `a ∈ Finset.filter p s ↔ a ∈ s ∧ p a`.

An element belongs to the filtered finset exactly when it belongs to the
original finset **and** satisfies the predicate. Use
`rw [Finset.mem_filter]` to convert a filter membership goal into a
conjunction. -/
TheoremDoc Finset.mem_filter as "Finset.mem_filter" in "Finset"

/-- `Finset.filter p s` returns the finset of elements of `s` satisfying `p`.

Given a finset `s : Finset α` and a predicate `p : α → Prop` with a
`DecidablePred` instance, `Finset.filter p s` is the sub-finset
`{x ∈ s | p x}`.

Use `Finset.mem_filter` to reason about membership. -/
DefinitionDoc Finset.filter as "Finset.filter"

NewTheorem Finset.mem_filter
NewDefinition Finset.filter
DisabledTactic trivial decide native_decide aesop simp_all
