import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 6

Title "List.Perm vs Equiv.Perm"

Introduction
"
# Two Notions of \"Permutation\"

The word **permutation** is used in two different ways in mathematics:

1. **A rearrangement relationship**: \"The list $[1, 0, 2]$ is a
   permutation of the list $[0, 1, 2]$.\" This is a *statement*
   comparing two lists.

2. **A bijection**: \"Let $\\sigma$ be a permutation of $\\{0, 1, 2\\}$.\"
   This is a *function* from the set to itself.

Lean and Mathlib formalize these as two distinct concepts, and confusing
them is a common source of errors.

## `List.Perm` — a relation on lists

`List.Perm l₁ l₂` (also written `l₁ ~ l₂`) is a **proposition**
asserting that `l₁` is a rearrangement of `l₂` — they contain the
same elements with the same multiplicities.

It is built inductively. One key constructor is:

```
List.Perm.swap : ∀ (x y : α) (l : List α), (y :: x :: l) ~ (x :: y :: l)
```

This says: swapping the first two elements of a list produces a
permutation.

## `Equiv.Perm` — a type of bijections

`Equiv.Perm α` is a **type** — the type of bijections from `α` to `α`.
An element `σ : Equiv.Perm α` is a *function* you can apply to elements.

## The distinction

| Concept | Type | Kind |
|---------|------|------|
| `List.Perm l₁ l₂` | `Prop` | A *relation* between two lists |
| `Equiv.Perm α` | `Type` | A *function type* (bijection `α → α`) |

They are fundamentally different: `List.Perm` compares two lists,
while `Equiv.Perm` *is* a function.

## Your task

Prove that the list `[1, 0, 2]` is a permutation of `[0, 1, 2]`
(as lists of `Fin 3`), using `List.Perm.swap`.
"

/-- The list `[1, 0, 2]` is a permutation of `[0, 1, 2]`. -/
Statement : ([1, 0, 2] : List (Fin 3)).Perm [0, 1, 2] := by
  Hint "The list `[1, 0, 2]` differs from `[0, 1, 2]` by a swap of the
  first two elements. Use `List.Perm.swap` to prove this.

  Recall: `List.Perm.swap x y l` proves `(y :: x :: l) ~ (x :: y :: l)`.

  Here `x = 0`, `y = 1`, `l = [2]`, giving `[1, 0, 2] ~ [0, 1, 2]`.

  Try `exact List.Perm.swap 0 1 [2]`."
  Hint (hidden := true) "Try `exact List.Perm.swap 0 1 [2]`."
  exact List.Perm.swap 0 1 [2]

Conclusion
"
You proved that two lists are permutations of each other using
`List.Perm.swap`.

## Why this matters

In informal mathematics, you might say both:
- \"$[1, 0, 2]$ is a permutation of $[0, 1, 2]$\" (list rearrangement)
- \"The permutation $(0\\;1)$ swaps $0$ and $1$\" (bijection)

These are related ideas, but in Lean they have completely different types:

- The first is `List.Perm [1, 0, 2] [0, 1, 2]` — a proof of a
  proposition. You *prove* it.
- The second is `Equiv.swap 0 1 : Equiv.Perm (Fin 3)` — a function.
  You *apply* it.

## Connecting the two

In advanced Mathlib, there are ways to convert between these notions
(e.g., every `Equiv.Perm` induces a `List.Perm` on the list of all
elements). But they serve different purposes:

- Use `List.Perm` when reasoning about *rearrangements of sequences*.
- Use `Equiv.Perm` when reasoning about *bijections and group structure*.

**In plain language**: \"`List.Perm` answers 'are these two lists
rearrangements of each other?' while `Equiv.Perm` answers 'what
bijection am I applying?' They are not the same thing.\"
"

/-- `List.Perm l₁ l₂` (notation: `l₁ ~ l₂`) is a proposition asserting
that `l₁` is a rearrangement of `l₂`: they contain the same elements
with the same multiplicities.

**Key constructors**:
- `List.Perm.nil : [].Perm []`
- `List.Perm.cons : a :: l₁ ~ a :: l₂` (from `l₁ ~ l₂`)
- `List.Perm.swap : (y :: x :: l) ~ (x :: y :: l)`
- `List.Perm.trans : l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`

**Contrast with `Equiv.Perm`**: `List.Perm` is a *relation* between
two lists (a `Prop`), while `Equiv.Perm α` is a *type* of bijections
(a `Type`). -/
DefinitionDoc List.Perm as "List.Perm"

/-- `List.Perm.swap x y l` proves that swapping the first two elements
of a list produces a permutation:

`(y :: x :: l).Perm (x :: y :: l)`

**When to use**: To prove that two lists differing by a swap of adjacent
elements are permutations of each other. -/
TheoremDoc List.Perm.swap as "List.Perm.swap" in "List"

NewDefinition List.Perm
NewTheorem List.Perm.swap
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
