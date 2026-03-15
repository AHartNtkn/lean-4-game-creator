import GameServer.Commands
import Mathlib

World "Capstone"
Level 1

Title "Warm-up: Fin + Finset"

Introduction
"
# Capstone: Integration

Welcome to the **final world** of the Finite Mathematics course!

## Looking back

Over the past 23 worlds, you have built a formidable toolkit:

| Module | Key concepts |
|--------|-------------|
| **Fin** | `Fin n`, constructors, case analysis |
| **Finset** | Membership, operations, cardinality, induction |
| **Fintype** | `Fintype.card`, compound types, pigeonhole |
| **Big operators** | `Finset.sum`, `Finset.prod`, splitting, reindexing |
| **Combinatorics** | Factorials, binomial coefficients, Pascal, binomial theorem |
| **Finsupp** | `Finsupp.single`, support, `Finsupp.sum` |
| **Matrix** | `Matrix` as functions, diagonal, transpose, multiplication |

This world integrates skills from **across the entire course**. Each
level draws on multiple modules. There are no new definitions or
theorems to learn -- only the challenge of combining what you already
know.

## Warm-up: Fin + Finset

Prove two facts:

1. Every element of `Fin 4` has value less than `4` (the `Fin` bound).
2. The finset `Finset.range 3` has exactly `3` elements.

For Part 1, use `intro x` and then `exact x.isLt` -- every `Fin n`
element carries its own bound proof.

For Part 2, use `exact Finset.card_range 3`.
"

/-- Every element of `Fin 4` is less than 4, and `Finset.range 3` has 3 elements. -/
Statement : (∀ x : Fin 4, x.val < 4) ∧ (Finset.range 3).card = 3 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "**Part 1**: For any `x : Fin 4`, `x.val < 4` is built into the type.

    Use `intro x` to introduce the element, then `exact x.isLt` to use
    the bound proof that every `Fin n` element carries."
    Hint (hidden := true) "Try `intro x` then `exact x.isLt`."
    intro x
    exact x.isLt
  · Hint "**Part 2**: Compute the cardinality of `Finset.range 3`.

    Use `exact Finset.card_range 3` to close the goal directly."
    Hint (hidden := true) "Try `exact Finset.card_range 3`."
    exact Finset.card_range 3

Conclusion
"
You combined two foundational skills:

- **Fin**: Each `x : Fin n` carries `x.isLt : x.val < n` as built-in data.
- **Finset**: `Finset.card_range n` evaluates `(Finset.range n).card = n`.

These are the building blocks that everything else in this course rests on.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
