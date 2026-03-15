import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 5

Title "Cardinality by induction"

Introduction
"
# Combining induction with cardinality

Now let's prove a cardinality result that uses the inductive hypothesis
`ih` in a meaningful way.

## The claim

Every finset has cardinality at most `s.card + 1` (trivially true, but
the proof exercises the pattern). Actually, let's prove something more
interesting: the converse of L03.

If `s = ∅`, then `s.card = 0`. This combines:
- A case for `∅`: directly compute `card ∅ = 0`.
- A case for `insert a s'`: derive a contradiction from the assumption
  that `insert a s'` is empty.

## Your task

Prove that if `s = ∅`, then `s.card = 0`, by finset induction.

This is simpler than L03 — but it completes the picture: together with
L03, you have shown `s.card = 0 ↔ s = ∅`.
"

/-- If a finset is empty, its cardinality is 0. -/
Statement {α : Type*} [DecidableEq α] (s : Finset α)
    (h : s = ∅) : s.card = 0 := by
  Hint "Start with `induction s using Finset.induction_on`."
  induction s using Finset.induction_on
  case empty =>
    Hint "The base case: `(∅ : Finset α).card = 0`.
    This is `Finset.card_empty`."
    Hint (hidden := true) "Use `rw [Finset.card_empty]`."
    rw [Finset.card_empty]
  case insert a s' ha ih =>
    Hint "You have `h : insert a s' = ∅`. But inserting an element
    never gives the empty set! This is a contradiction.

    The lemma `Finset.insert_ne_empty` states that
    `insert a s ≠ ∅`. Use `exact absurd h (Finset.insert_ne_empty a s')`."
    Hint (hidden := true) "Use `exact absurd h (Finset.insert_ne_empty a s')`."
    exact absurd h (Finset.insert_ne_empty a s')

Conclusion
"
You proved that if `s = ∅`, then `s.card = 0`.

## The iff picture

Together with L03, you now have both directions:

- **L03**: `s.card = 0 → s = ∅` (by finset induction, contradicting
  `card + 1 = 0` in the insert case)
- **L05**: `s = ∅ → s.card = 0` (by finset induction, contradicting
  `insert a s' = ∅` in the insert case)

In mathlib, these are combined as `Finset.card_eq_zero : s.card = 0 ↔ s = ∅`.

## Another contradiction pattern

In L03, the contradiction was *arithmetic*: `s'.card + 1 = 0`.
In this level, the contradiction was *structural*: `insert a s' = ∅`.

Both are valid. The choice depends on what assumptions you have.

**In plain language**: \"The empty set has zero elements. Any set formed
by insertion has at least one element, so it cannot be empty.\"
"

/-- `Finset.insert_ne_empty a s` states that `insert a s ≠ ∅`.

Inserting an element into a finset never produces the empty finset. -/
TheoremDoc Finset.insert_ne_empty as "Finset.insert_ne_empty" in "Finset"

NewTheorem Finset.insert_ne_empty
DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.card_eq_zero
