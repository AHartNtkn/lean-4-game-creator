import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 1

Title "Build it three ways"

Introduction
"
# Building and Inspecting {1, 2, 3, 4, 5}

Welcome to a concrete exploration world. Instead of learning new theory,
you will work with a single finset -- `{1, 2, 3, 4, 5}` -- and apply
every finset operation you have learned so far.

## Three ways to build {1, 2, 3, 4, 5}

There are (at least) three ways to construct this finset:

1. **Literal notation**: `{1, 2, 3, 4, 5}`. This is syntactic sugar for
   iterated `insert`:
   `insert 1 (insert 2 (insert 3 (insert 4 {5})))`.

2. **Explicit iterated insert**: Build the finset step by step, starting
   from the singleton `{5}` and inserting 4, 3, 2, 1 in turn. This is
   literally what the notation desugars to.

3. **`Finset.range` with `Finset.image`**: `Finset.range 5` gives
   `{0, 1, 2, 3, 4}`. Applying `Finset.image (· + 1)` shifts every
   element up by one, producing `{1, 2, 3, 4, 5}`.

## Your task

Prove two equalities:
1. The iterated-insert form equals the literal form (this is definitional).
2. `Finset.image (· + 1) (Finset.range 5) = {1, 2, 3, 4, 5}`.

Split with `constructor`, then handle each part.
"

/-- The finset {1,2,3,4,5} can be built by iterated insert or by shifting a range. -/
Statement : insert 1 (insert 2 (insert 3 (insert 4 ({5} : Finset Nat)))) =
    ({1, 2, 3, 4, 5} : Finset Nat) ∧
    Finset.image (· + 1) (Finset.range 5) = ({1, 2, 3, 4, 5} : Finset Nat) := by
  Hint "The goal is a conjunction. Split it with `constructor`."
  constructor
  · Hint "The first goal asks whether the iterated-insert form equals the
    literal. But the literal notation *is* syntactic sugar for
    `insert 1 (insert 2 (insert 3 (insert 4 ...)))`. So both sides are
    definitionally equal."
    Hint (hidden := true) "Try `rfl`. The two expressions are the same by
    definition."
    rfl
  · Hint "The second goal asks whether
    `Finset.image (· + 1) (Finset.range 5)` equals the literal finset.
    This is not definitional -- Lean needs to compute the image. Use
    `ext x` to reduce to a membership equivalence."
    Hint (hidden := true) "Use `ext x` to reduce to membership, then
    `simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]` and handle each direction."
    ext x
    Hint "After `ext`, the goal asks: for each `x`, is
    `x ∈ Finset.image (· + 1) (Finset.range 5)` iff `x` is in the literal
    finset? Use `simp only` with the relevant membership lemmas, then
    split the biconditional."
    Hint (hidden := true) "Use `simp only [Finset.mem_image, Finset.mem_range,
    Finset.mem_insert, Finset.mem_singleton]` then `constructor`."
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_insert,
      Finset.mem_singleton]
    Hint "The goal is now a biconditional between an existential
    (from `mem_image`) and a disjunction (from the literal finset).
    Use `constructor` and handle each direction."
    Hint (hidden := true) "Use `constructor`. For the forward direction,
    `rintro ⟨a, ha, rfl⟩` then `omega`. For the backward direction,
    `rintro (rfl | rfl | rfl | rfl | rfl)` then provide witnesses."
    constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · rintro (rfl | rfl | rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩

Conclusion
"
You built `{1, 2, 3, 4, 5}` two ways and proved they are the same finset:

1. **Literal / iterated insert**: `rfl` sufficed because the literal notation
   *is* iterated insert.
2. **Range + image**: `Finset.range 5 = {0, 1, 2, 3, 4}`, and
   `Finset.image (· + 1)` shifts each element up by one. This required
   `ext` + membership reasoning.

## Why `Finset.range` matters

The range-and-shift construction is the standard way to build arithmetic
sequences as finsets. You will see `Finset.range n` extensively when
working with big operators (`Finset.sum`, `Finset.prod`) in later worlds.

**In plain language**: \"The set {1, 2, 3, 4, 5} can be described as the
set of natural numbers from 1 to 5, or equivalently, as the set of values
obtained by adding 1 to each element of {0, 1, 2, 3, 4}.\"
"

/-- `Finset.range n` is the finset `{0, 1, 2, ..., n-1}`.

It contains exactly the natural numbers less than `n`. Use
`Finset.mem_range` to reason about membership: `a ∈ Finset.range n ↔ a < n`.

**Warning**: `Finset.range n` contains `0` through `n - 1`, not `1` through `n`. -/
DefinitionDoc Finset.range as "Finset.range"

NewDefinition Finset.range
DisabledTactic trivial decide native_decide aesop simp_all
