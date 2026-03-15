import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 6

Title "Boss: Convert between notions"

Introduction
"
# Boss: A Finiteness Conversion Proof

Time to integrate everything from this world. You will prove two facts
about `Fin 4` that require converting between all three notions of
finiteness.

## Part 1: Membership

Prove that every element of `Fin 4` belongs to `Set.finite_univ.toFinset`.

This requires:
- `Set.Finite.mem_toFinset` (Level 4) to convert finset membership to
  set membership.
- `Set.mem_univ` to show that every element belongs to `Set.univ`.

## Part 2: Cardinality

Prove that `Set.finite_univ.toFinset.card = 4`.

This requires chaining conversions:
1. `Set.Finite.toFinset_eq_toFinset` to switch to `Set.toFinset` (Level 5).
2. `Set.toFinset_univ` to connect to `Finset.univ` (Level 5).
3. `Finset.card_univ` to connect to `Fintype.card` (from the Fintype world).
4. `Fintype.card_fin` to evaluate the cardinality (from the Fintype world).

## Your task

Prove both parts as a conjunction.
"

/-- Every `Fin 4` is in `Set.finite_univ.toFinset`, and that finset has 4 elements. -/
Statement : (∀ x : Fin 4, x ∈ (Set.finite_univ (α := Fin 4)).toFinset) ∧
    (Set.finite_univ (α := Fin 4)).toFinset.card = 4 := by
  Hint "This is a conjunction. Split it with `constructor`."
  constructor
  · Hint "For the first part, introduce `x` and convert finset membership
    to set membership.
    Try `intro x` then `rw [Set.Finite.mem_toFinset]`."
    intro x
    Hint "Now use `Set.Finite.mem_toFinset` to convert
    `x ∈ Set.finite_univ.toFinset` to `x ∈ Set.univ`."
    rw [Set.Finite.mem_toFinset]
    Hint "The goal is `x ∈ Set.univ`. Every element belongs to the
    universal set. Use `exact Set.mem_univ x`."
    Hint (hidden := true) "Use `exact Set.mem_univ x`."
    exact Set.mem_univ x
  · Hint "For the second part, you need to chain four rewrites to convert
    `Set.finite_univ.toFinset.card` all the way to `4`.

    Start with `rw [Set.Finite.toFinset_eq_toFinset]` to switch
    from `Set.Finite.toFinset` to `Set.toFinset`."
    rw [Set.Finite.toFinset_eq_toFinset]
    Hint "Now use `rw [Set.toFinset_univ]` to connect `Set.univ.toFinset`
    to `Finset.univ`."
    rw [Set.toFinset_univ]
    Hint "Now use `rw [Finset.card_univ]` to convert `Finset.univ.card`
    to `Fintype.card (Fin 4)`."
    rw [Finset.card_univ]
    Hint "Finally, use `rw [Fintype.card_fin]` to evaluate `Fintype.card (Fin 4)` to `4`."
    Hint (hidden := true) "Use `rw [Fintype.card_fin]` (or `exact Fintype.card_fin 4`)."
    rw [Fintype.card_fin]

Conclusion
"
Congratulations on completing the Three Notions of Finiteness world!

You proved both membership and cardinality for `Set.finite_univ.toFinset`,
using conversions that chain through all three notions:

**Membership chain**:
`Set.finite_univ.toFinset` → `mem_toFinset` → `Set.univ` → `mem_univ`

**Cardinality chain**:
`Set.finite_univ.toFinset.card` → `toFinset_eq_toFinset` →
`Set.univ.toFinset.card` → `toFinset_univ` →
`Finset.univ.card` → `card_univ` →
`Fintype.card (Fin 4)` → `card_fin` → `4`

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| `Set.Finite` definition | L01 | `Set.Finite`, `Set.toFinite` |
| `Fintype` → `Set.Finite` | L02 | `Set.finite_univ` |
| `Finset` → `Set.Finite` | L03 | `Finset.finite_toSet` |
| `Set.Finite` → `Finset` | L04 | `Set.Finite.toFinset`, `mem_toFinset` |
| The two `toFinset`s agree | L05 | `toFinset_eq_toFinset`, `toFinset_univ` |
| Integration | L06 | All of the above |

## Transfer moment

In ordinary mathematics, the distinction between \"this set is finite,\"
\"this type is finite,\" and \"here is a finite collection\" is rarely
made explicit. Mathematicians freely move between these perspectives.

In Lean, these are three distinct concepts with different types and
different APIs. The conversion lemmas you learned in this world are the
formal counterparts of the implicit steps a mathematician makes when
they say \"since $S$ is finite, we can enumerate its elements.\"

Understanding which notion to use and how to convert between them is
a practical skill for formalizing finiteness arguments in Lean.

## What comes next

The next worlds build on these foundations to work with finitely supported
functions (`Finsupp`), permutations, and other structures that require
choosing the right notion of finiteness.
"

TheoremTab "Set"
DisabledTactic trivial decide native_decide simp aesop simp_all
