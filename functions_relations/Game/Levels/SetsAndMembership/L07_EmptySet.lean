import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 7

Title "The Empty Set"

Introduction
"
The **empty set** `∅` is the set with no elements. In Lean,
`x ∈ ∅` is definitionally `False`. No element belongs to the empty set.

This has an immediate consequence: the empty set is a subset of every
set. Why? Because `∅ ⊆ A` means `∀ x, x ∈ ∅ → x ∈ A`, and the
hypothesis `x ∈ ∅` is `False`. From `False`, anything follows — this
is **vacuous truth**.

After `intro x hx`, the hypothesis `hx : x ∈ ∅` is actually
`hx : False`. You have a contradiction! Use `contradiction` to close
the goal. (You may remember `contradiction` from the Natural Numbers
Game — it closes any goal when a hypothesis is `False` or when two
hypotheses directly contradict each other.)

**New definition**: `∅` — the empty set.
"

/-- `∅` is the empty set. For any type `α`, `∅ : Set α` is the set
containing no elements. Membership `x ∈ ∅` is definitionally equal
to `False`.

To use a hypothesis `h : x ∈ ∅` (which is really `h : False`),
use `contradiction` — it detects the `False` hypothesis and closes
any goal. Alternatively, `exact h.elim` or `exact False.elim h` work. -/
DefinitionDoc EmptyCollection.emptyCollection as "∅ (sets)"

NewDefinition EmptyCollection.emptyCollection

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem Set.empty_subset bot_le

Statement (A : Set ℕ) : ∅ ⊆ A := by
  Hint "Start with the standard subset pattern: `intro x hx`."
  intro x hx
  Hint "Look at `hx`: it says `x ∈ ∅`. But `∅` is the set where membership
  is `False`. So `hx` is actually a proof of `False`!

  From `False`, anything follows. Try `contradiction` to close the goal.
  (Alternatively, `exact hx.elim` also works — the `.elim` method on
  `False` says: from a proof of `False`, derive anything.)"
  contradiction

Conclusion
"
The empty set is a subset of every set because the subset condition
`∀ x, x ∈ ∅ → x ∈ A` is *vacuously true* — there are no elements
in `∅`, so the hypothesis `x ∈ ∅` is `False`, and `False → anything`
is always true.

This is a pattern worth remembering: when a hypothesis is `x ∈ ∅`,
you have a contradiction.

**Key fact**: `x ∈ ∅` is definitionally `False`.
"
