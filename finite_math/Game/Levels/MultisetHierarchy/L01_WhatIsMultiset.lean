import GameServer.Commands
import Mathlib

World "MultisetHierarchy"
Level 1

Title "What is a Multiset?"

Introduction
"
# From Lists to Multisets

In the previous world, you learned about `List` -- an ordered sequence
that allows duplicates. Now we take the first step up the hierarchy:
**multisets**.

## The key idea

A `Multiset α` is a collection of elements of type `α` that:
- **remembers multiplicity** (how many times each element appears), but
- **forgets order** (the arrangement of elements does not matter).

In Lean / mathlib, `Multiset α` is defined as a **quotient**:

```
Multiset α := Quot (List.Perm)
```

This means: a multiset is an equivalence class of lists under the
permutation relation. Two lists that are rearrangements of each other
represent the same multiset.

## The coercion `↑`

Given a list `l : List α`, you can convert it to a multiset by writing
`(↑l : Multiset α)`. This is a coercion -- it wraps the list into its
equivalence class. From this point forward, the order information is gone.

## Your task

Prove that converting `[1, 2, 3]` to a multiset and computing its
cardinality gives `3`.

Since `Multiset.card` on a coerced list is **definitionally equal** to
`List.length`, `rfl` will work. This is not a coincidence -- `Multiset.card`
is designed so that `card (↑l) = l.length` holds by definition, without
needing any lemma.
"

/-- The multiset obtained from `[1, 2, 3]` has cardinality 3. -/
Statement : Multiset.card (↑([1, 2, 3] : List Nat) : Multiset Nat) = 3 := by
  Hint "Look at both sides of the goal. The left side, `Multiset.card (↑[1, 2, 3])`,
  reduces to `List.length [1, 2, 3]`, which is `3`. The right side is also `3`.
  When both sides are definitionally equal, what tactic proves the equality?"
  Hint (hidden := true) "Try `rfl`. It works because `Multiset.card` on a coerced
  list is definitionally equal to the list's length."
  rfl

Conclusion
"
When you coerce a list to a multiset with `↑`, the **cardinality is preserved**:
`Multiset.card (↑l) = l.length` for any list `l`. This is a **definitional equality**,
which is why `rfl` works -- Lean does not need a lemma to verify it, just unfolding.

The distinction between definitional equality (provable by `rfl`) and propositional
equality (requiring `rw` or other tactics) is fundamental in Lean. Here, the fact
that `Multiset.card` is defined in terms of `List.length` makes this definitional.

The key difference between a list and a multiset is that **order is forgotten**.
The lists `[1, 2, 3]` and `[3, 1, 2]` are different as lists, but they become the
same multiset when coerced with `↑`. You will see this in the next levels.

**In plain language**: A multiset is a \"bag\" of elements. You know what is
inside and how many of each, but there is no first or last element -- just
a collection.
"

/-- `Multiset α` is the type of finite multisets of elements of type `α`.
A multiset remembers **how many times** each element appears (multiplicity)
but **forgets the order**. It is defined as a quotient of `List α` by the
permutation relation.

Construct a multiset from a list using the coercion `↑`: given `l : List α`,
write `(↑l : Multiset α)`. -/
DefinitionDoc Multiset as "Multiset"

/-- `Multiset.card m` returns the number of elements in multiset `m`,
counting multiplicity. For a coerced list, `Multiset.card (↑l) = l.length`
holds definitionally (provable by `rfl`). -/
DefinitionDoc Multiset.card as "Multiset.card"

/-- `trivial` attempts to close a goal using simple methods including
`assumption`, `rfl`, and `Decidable` evaluation. On small finite types,
it can solve goals automatically without showing any proof steps.

In this course, `trivial` is disabled so that you practice the manual
proof patterns. -/
TacticDoc trivial

/-- `native_decide` is like `decide` but uses compiled native code for
evaluation instead of the kernel. It is faster but less trustworthy.

In this course, `native_decide` is disabled so that you practice
symbolic proof techniques. -/
TacticDoc native_decide

/-- `aesop` (Automated Extensible Search for Obvious Proofs) is a powerful
automation tactic that searches for proofs using a configurable set of rules.
It can solve many goals automatically but provides no insight into the proof.

In this course, `aesop` is disabled so that you learn the underlying proof steps. -/
TacticDoc aesop

/-- `simp_all` applies the `simp` tactic to all hypotheses and the goal
simultaneously. It is more aggressive than `simp` and can close many goals.

In this course, `simp_all` is disabled to encourage step-by-step reasoning. -/
TacticDoc simp_all

NewDefinition Multiset Multiset.card
DisabledTactic trivial decide native_decide simp aesop simp_all
