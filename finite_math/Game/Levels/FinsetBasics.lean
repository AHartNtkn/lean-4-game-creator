import Game.Levels.FinsetBasics.L01_WhatIsAFinset
import Game.Levels.FinsetBasics.L02_FindingDeeperElements
import Game.Levels.FinsetBasics.L03_TheEmptyFinset
import Game.Levels.FinsetBasics.L04_RangeOfNaturals
import Game.Levels.FinsetBasics.L05_TheRangeBoundary
import Game.Levels.FinsetBasics.L06_RangeEmpty
import Game.Levels.FinsetBasics.L07_VariableRange
import Game.Levels.FinsetBasics.L08_RangeReverseDirection
import Game.Levels.FinsetBasics.L09_FinToFinsetBridge
import Game.Levels.FinsetBasics.L10_FinsetToFinBridge
import Game.Levels.FinsetBasics.L11_GeneralNonMembership
import Game.Levels.FinsetBasics.L12_ProvingNonMembership
import Game.Levels.FinsetBasics.L13_ReadingMembership
import Game.Levels.FinsetBasics.L14_InsertIsIdempotent
import Game.Levels.FinsetBasics.L15_NonemptyFinsets
import Game.Levels.FinsetBasics.L16_ProvingNonempty
import Game.Levels.FinsetBasics.L17_DecideShortcut
import Game.Levels.FinsetBasics.L18_Boss

World "FinsetBasics"
Title "Finset Basics"

Introduction "
# Finset Basics: Finite Sets

In Phase 1, you learned about `Fin n` — a finite *index type* where
each element is a number with a bound proof. Functions `Fin n → α`
gave you *ordered tuples*: data accessed by position.

But not everything in mathematics has a natural ordering. The set of
prime divisors of 30 is $\\{2, 3, 5\\}$ — there's no reason 2 should
come 'first'. The elements of a group satisfying some property form a
*collection defined by membership*, not by position.

This is where `Finset` comes in. A `Finset α` is an **unordered finite
collection** of elements from `α`, with no duplicates and decidable
membership. Think of it as a mathematical finite set, formalized.

The key operations:
- **Literal notation**: `\\{1, 2, 3\\}` builds a concrete finset
- **`∅`**: the empty finset
- **`insert a s`**: add an element (no-op if already present)
- **`Finset.range n`**: the set $\\{0, 1, \\ldots, n-1\\}$

The key proof move: to show `x ∈ s`, unfold the set structure using
*membership lemmas* (`Finset.mem_insert`, `Finset.mem_singleton`,
`Finset.mem_range`) until the goal reduces to something `rfl` or
`omega` can close.

The bridge from Phase 1: `Finset.range n` contains exactly the same
elements as `Fin n` — the numbers $0$ through $n-1$. Where `Fin n`
gave you *indexed access* (`f i` for `i : Fin n`), `Finset.range n`
gives you *membership* (`k ∈ Finset.range n ↔ k < n`). Same elements,
different interface.

In this world you'll learn to prove membership, non-membership,
and basic structural facts about finsets. The boss at the end
combines all these moves.
"
