import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 1

Title "The empty finset"

Introduction
"
# Constructing Finsets

In the previous worlds, you saw finsets arise as the output of `toFinset` --
they appeared at the end of the `List → Multiset → Finset` pipeline. Now we
change perspective: instead of *arriving* at a finset from below, we will
**construct finsets directly**.

## Why this matters

In mathematics, we often define finite sets by listing their elements:
$\\{1, 2, 3\\}$, $\\{a, b\\}$, or $\\emptyset$. In Lean, the `Finset` type
provides the same capability, but the construction mechanism is more explicit.
Understanding *how* finsets are built will prepare you to prove things *about*
finsets in later worlds.

## The empty finset

The simplest finset is the empty one. In Lean, there are two ways to write it:

- `Finset.empty` -- the explicit constructor
- `∅` or `{}` -- notation

Both refer to the same object: a finset with no elements.

## Your task

Prove that `Finset.empty` and `∅` are the same finset. This is true by
definition -- they are literally the same thing, so `rfl` will work.
"

/-- The empty finset `Finset.empty` equals `∅`. -/
Statement : (Finset.empty : Finset Nat) = ∅ := by
  Hint "Both sides of this equation are definitionally the same object.
  `Finset.empty` is the explicit name, and `∅` is the notation for it.
  What tactic proves definitional equalities?"
  Hint (hidden := true) "Try `rfl`. Since `∅` is just notation for
  `Finset.empty`, both sides are identical."
  rfl

Conclusion
"
The empty finset is the starting point for building all other finsets.
Every finset can be constructed by starting from `∅` and adding elements
one at a time (using `insert`, which you will learn shortly).

This is analogous to how every list can be built from `[]` using `::`,
and every natural number can be built from `0` using `succ`. The empty
finset is the **base case** of finset construction.

**Notation**: In Lean, `∅` and `{}` both refer to `Finset.empty`. You
will see both in mathlib. We will use `∅` when emphasizing emptiness
and `{a, b, c}` notation when listing specific elements.

**In plain language**: \"The empty set has no elements. In Lean, it is
written `∅` or `Finset.empty`.\"
"

/-- `Finset.empty` is the finset with no elements. It is written `∅` or `{}`.
Every finset can be built starting from `Finset.empty` and adding elements
with `insert`.

In a proof, `Finset.empty` appears as `∅` in the goal state. -/
DefinitionDoc Finset.empty as "Finset.empty"

/-- `Finset α` is the type of finite sets of elements of type `α`. Unlike
`Set α`, a `Finset` is computationally finite -- it carries an explicit
list of its elements (with no duplicates).

A `Finset α` consists of a `Multiset α` (the underlying collection) together
with a proof that the multiset has no duplicates (`Multiset.Nodup`).

Construct finsets using:
- `∅` or `Finset.empty` for the empty finset
- `{a}` or `Finset.singleton a` for a singleton
- `insert a s` to add an element
- `{a, b, c}` notation for literal finsets -/
DefinitionDoc Finset as "Finset"

NewDefinition Finset Finset.empty
DisabledTactic trivial decide native_decide simp aesop simp_all
