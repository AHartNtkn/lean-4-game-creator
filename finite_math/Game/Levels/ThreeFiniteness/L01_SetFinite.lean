import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 1

Title "Set.Finite: A set can be finite"

Introduction
"
# Three Notions of Finiteness

In Lean and Mathlib there are *three* different ways to express that
something is finite:

1. **`Set.Finite`** — a *predicate* on a set (a `Prop`).
2. **`Fintype`** — a *type class* on a type.
3. **`Finset`** — a *data type* representing a concrete finite collection.

Each serves a different purpose, and knowing when to use which is an
important skill. This world introduces all three, explains their
relationships, and shows you how to convert between them.

## `Set.Finite`

Given a set `s : Set α`, the proposition `s.Finite` (or `Set.Finite s`)
asserts that `s` has finitely many elements. It is a *predicate*: it
lives in `Prop`, and it carries no computational data about what those
elements are or how to enumerate them.

## Key lemmas

For concrete sets, two lemmas are often enough:

- `Set.finite_singleton : {a}.Finite` — a singleton set is finite.
- `Set.finite_insert : (insert a s).Finite ↔ s.Finite` — inserting
  an element preserves finiteness (in both directions).

There is also a convenience lemma:
- `Set.toFinite : [Finite ↑s] → s.Finite` — if Lean can automatically
  see the set is finite, `Set.toFinite s` gives you a proof.

## Your task

Prove that the set `{1, 2, 3}` of natural numbers is finite.

Recall that `{1, 2, 3}` is notation for `insert 1 (insert 2 {3})`.
So you can strip away elements one at a time with `Set.finite_insert`,
then finish with `Set.finite_singleton`.

Alternatively, `exact Set.toFinite _` lets Lean figure it out automatically.
"

/-- The set `{1, 2, 3}` is finite. -/
Statement : ({1, 2, 3} : Set Nat).Finite := by
  Hint "The set is `insert 1 (insert 2 (singleton 3))`.
  You can peel off the first element with `rw [Set.finite_insert]`,
  reducing the goal to `(insert 2 (singleton 3)).Finite`.

  Alternatively, `exact Set.toFinite _` closes the goal in one step."
  Hint (hidden := true) "Use `exact Set.toFinite _` for a one-line proof.
  Or use `rw [Set.finite_insert]` twice, then `exact Set.finite_singleton 3`."
  exact Set.toFinite _

Conclusion
"
You proved that `{1, 2, 3}` is a finite set.

## Two proof strategies

**The automatic way**: `Set.toFinite _` works whenever Lean can infer
a `Finite` instance on the subtype `↑s`. For literal sets of natural
numbers, this is always the case.

**The structural way**: Since `{1, 2, 3} = insert 1 (insert 2 {3})`,
you can use `Set.finite_insert` (an iff) to strip insertions one by one,
then `Set.finite_singleton` to close the base case. This is more explicit
but teaches you how `Set.Finite` interacts with set operations.

## What `Set.Finite` is *not*

`Set.Finite s` lives in `Prop`. It tells you the set is finite, but it
does **not** give you a way to enumerate the elements or compute the
cardinality. For that, you need to convert to a `Finset` (which we will
do in Level 4).

**In plain language**: \"`Set.Finite` is a certificate of finiteness.
It says 'this set is finite' without saying how to list its elements.\"
"

/-- `Set.Finite s` is a predicate asserting that the set `s` has finitely
many elements.

**Key lemmas**:
- `Set.finite_singleton : {a}.Finite`
- `Set.finite_insert : (insert a s).Finite ↔ s.Finite`
- `Set.finite_empty : (∅ : Set α).Finite`
- `Set.toFinite : [Finite ↑s] → s.Finite`

**When to use**: When you want to assert that a subset of a type is finite,
without needing to enumerate its elements. -/
DefinitionDoc Set.Finite as "Set.Finite"

/-- `Set.toFinite s` produces a proof of `s.Finite` from a `Finite` instance
on the subtype `↑s`. This is the easiest way to prove `Set.Finite` for
concrete sets.

**Type**: `Set.toFinite (s : Set α) [Finite ↑s] : s.Finite` -/
TheoremDoc Set.toFinite as "Set.toFinite" in "Set"

/-- `Set.finite_singleton a` proves that the singleton set `{a}` is finite.

**Type**: `Set.finite_singleton (a : α) : ({a} : Set α).Finite` -/
TheoremDoc Set.finite_singleton as "Set.finite_singleton" in "Set"

/-- `Set.finite_insert` is the equivalence stating that inserting an element
preserves finiteness: `(insert a s).Finite ↔ s.Finite`.

Use `rw [Set.finite_insert]` to strip an `insert` from the goal. -/
TheoremDoc Set.finite_insert as "Set.finite_insert" in "Set"

NewDefinition Set.Finite
NewTheorem Set.toFinite Set.finite_singleton Set.finite_insert
DisabledTactic trivial decide native_decide simp aesop simp_all
