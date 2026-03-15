import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 5

Title "Cardinality and insertion"

Introduction
"
# Insertion can increase cardinality by at most 1

You know two lemmas about the cardinality of `insert a s`:

- `Finset.card_insert_of_notMem : a ∉ s → (insert a s).card = s.card + 1`
- `Finset.card_insert_of_mem : a ∈ s → (insert a s).card = s.card`

In either case, `(insert a s).card ≤ s.card + 1`. This is the lemma
`Finset.card_insert_le`.

## Proof strategy: by_cases

When a property depends on whether `a ∈ s` or `a ∉ s`, you can split
into cases with `by_cases h : a ∈ s`:

- **Case `h : a ∈ s`**: Use `card_insert_of_mem` to show
  `(insert a s).card = s.card`, then `omega`.
- **Case `h : a ∉ s`**: Use `card_insert_of_notMem` to show
  `(insert a s).card = s.card + 1`, which is exactly `≤ s.card + 1`.

## Your task

Prove `(insert a s).card ≤ s.card + 1` using `by_cases`.
"

/-- Inserting an element increases cardinality by at most 1. -/
Statement {α : Type*} [DecidableEq α] (a : α) (s : Finset α) :
    (insert a s).card ≤ s.card + 1 := by
  Hint "Split into cases with `by_cases h : a ∈ s`."
  by_cases h : a ∈ s
  · Hint "In this case, `h : a ∈ s`. Inserting a duplicate does not
    change the cardinality. Use `rw [Finset.card_insert_of_mem h]`."
    Hint (hidden := true) "After `rw [Finset.card_insert_of_mem h]`,
    the goal becomes `s.card ≤ s.card + 1`. Use `omega`."
    rw [Finset.card_insert_of_mem h]
    omega
  · Hint "In this case, `h : a ∉ s`. Inserting a new element increases
    the cardinality by exactly 1. Use `rw [Finset.card_insert_of_notMem h]`."
    rw [Finset.card_insert_of_notMem h]

Conclusion
"
You proved `card_insert_le` by case analysis on membership.

## Why this matters for induction

This result will be essential in the boss level, where you prove
`(s ∪ t).card ≤ s.card + t.card` by finset induction. In the inductive
step, you will need to bound `card (insert a ...)`, and `card_insert_le`
provides exactly that bound.

## `by_cases` vs induction

This proof used `by_cases` (case analysis on membership), not finset
induction. Both are valid proof strategies for finset problems:

- **Finset induction**: Build up from `∅` by inserting elements. Best
  when the property is about *all finsets* and decomposes along the
  insert structure.
- **by_cases on membership**: Split on whether a specific element is in
  a specific set. Best when the property depends on membership of a
  *particular* element.

Knowing when to use which is a key skill.

**In plain language**: \"Adding an element to a set increases its size
by at most 1 — either 0 (if the element was already there) or 1 (if
it was new).\"
"

/-- `Finset.card_insert_le` states that
`(insert a s).card ≤ s.card + 1`.

Inserting an element increases the cardinality by at most 1. This is
disabled here so you can prove it yourself using `by_cases`. -/
TheoremDoc Finset.card_insert_le as "Finset.card_insert_le" in "Finset"

/-- `Finset.insert_union` states that `insert a s ∪ t = insert a (s ∪ t)`.

Inserting into the left side of a union is the same as inserting into
the union. This is useful in induction proofs where you need to decompose
a union at the `insert` boundary. -/
TheoremDoc Finset.insert_union as "Finset.insert_union" in "Finset"

NewTheorem Finset.insert_union
DisabledTactic trivial decide native_decide aesop simp_all
DisabledTheorem Finset.card_insert_le
