import GameServer.Commands
import Mathlib

World "FinIntro"
Level 6

Title "Fin 1 is a singleton"

Introduction
"
# The one-element type `Fin 1`

`Fin 1` contains exactly one element: the number `0` (with proof `0 < 1`).

This means any two elements of `Fin 1` must be equal -- there is only
one possibility!

## Subtype extensionality in action

To prove two elements of `Fin n` are equal, it suffices to show their
underlying natural numbers are equal. The tactic approach:

1. Use `ext` to reduce `a = b` to `a.val = b.val`
2. Prove the resulting arithmetic goal

Since both `a.val` and `b.val` are natural numbers less than `1`, they
must both be `0`.

## Your task

Prove that all elements of `Fin 1` are equal. You are given two arbitrary
elements `a` and `b` of `Fin 1` and must show `a = b`.
"

/-- `Fin 1` has exactly one element: all elements are equal. -/
Statement (a b : Fin 1) : a = b := by
  Hint "Use `ext` to reduce this to showing `a.val = b.val`."
  ext
  Hint "Now you need `a.val = b.val` where both are natural numbers less than 1. Try `omega`."
  omega

Conclusion
"
Since the only natural number less than `1` is `0`, both `a.val` and
`b.val` must be `0`, so `a = b`.

Let's contrast the boundary cases:
- `Fin 0` has **0 elements** (empty type)
- `Fin 1` has **1 element** (the number `0`)
- `Fin 2` has **2 elements** (`0` and `1`)
- `Fin n` has **n elements** (`0, 1, ..., n-1`)

Notice that the elements of `Fin n` are `0` through `n - 1`, not `1`
through `n`. This zero-indexing is important -- the largest element of
`Fin n` is `n - 1`, not `n`.

The `ext` tactic works for `Fin` equality, but it is a *general-purpose*
tactic. It applies whenever two objects are equal if their components are
equal. You will see `ext` again when proving equality of finsets, functions,
and other structured types.

**In plain language**: \"The only natural number less than 1 is 0, so the
set $\\{i \\in \\mathbb{N} \\mid i < 1\\}$ is the singleton $\\{0\\}$.\"
"
