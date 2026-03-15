import GameServer.Commands
import Mathlib

World "ListUnderLenses"
Level 1

Title "As a List"

Introduction
"
# One Object, Three Lenses

Welcome to a different kind of world. Instead of learning new theory,
you will study **one concrete piece of data** -- the list `[1, 2, 1, 3]` --
and examine it through three different mathematical lenses:
1. **List**: ordered, duplicates allowed
2. **Multiset**: unordered, duplicates allowed
3. **Finset**: unordered, no duplicates

By the end, you will have a visceral understanding of what information
each representation keeps and what it discards.

## The list lens

As a list, `[1, 2, 1, 3]` has:
- **Length 4**: four elements, counting duplicates and respecting order.
- **Order matters**: the first element is `1`, the second is `2`, the third
  is `1` again, and the fourth is `3`.
- **Duplicates matter**: the `1` at position 0 and the `1` at position 2
  are distinct entries.

## Your task

Prove two basic facts about `[1, 2, 1, 3]` as a list:
1. Its length is 4.
2. The element `2` is a member of the list.

Use `constructor` to split the conjunction, then handle each part.
"

/-- The list `[1, 2, 1, 3]` has length 4 and contains 2. -/
Statement : ([1, 2, 1, 3] : List Nat).length = 4 ∧
    (2 : Nat) ∈ ([1, 2, 1, 3] : List Nat) := by
  Hint "The goal is a conjunction (`∧`). Use `constructor` to split it into
  two subgoals."
  constructor
  · Hint "The first goal asks about the length of a concrete list.
    `List.length [1, 2, 1, 3]` reduces to `4` by definition.
    What tactic proves a definitional equality?"
    Hint (hidden := true) "Try `rfl`. The length of a concrete list is
    computed by definition."
    rfl
  · Hint "The second goal asks whether `2 ∈ [1, 2, 1, 3]`. This is a
    concrete membership check in a finite list. What tactic can evaluate
    decidable propositions on concrete data?"
    Hint (hidden := true) "Try `decide`. It evaluates the membership check
    by scanning through the list."
    decide

Conclusion
"
Two observations about the **list** lens:

1. **Length**: `List.length [1, 2, 1, 3] = 4`. The duplicate `1` counts
   twice. If `1` appeared only once, the length would be 3.

2. **Membership**: `2 ∈ [1, 2, 1, 3]` holds because `2` appears in the
   list (at index 1). The `decide` tactic scans through the list elements
   and finds a match.

**Proof moves used**:
- `constructor` to split the conjunction
- `rfl` for definitional equality (length computation)
- `decide` for decidable proposition (membership check)

**In plain language**: \"The sequence 1, 2, 1, 3 has four entries. The
number 2 appears among them.\"

In the next level, you will look at the same data through the **multiset**
lens and see what changes -- and what does not.
"

DisabledTactic trivial native_decide simp aesop simp_all
