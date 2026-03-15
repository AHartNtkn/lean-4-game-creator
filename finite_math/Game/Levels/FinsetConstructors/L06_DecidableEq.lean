import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 6

Title "Why DecidableEq matters"

Introduction
"
# The hidden requirement: `DecidableEq`

Every finset operation you have used so far -- `insert`, `singleton`,
membership testing -- works on `Finset Nat`. But could you build a
`Finset` of *any* type? Not quite.

## The problem

A `Finset α` is a multiset with no duplicates. To check whether an
element is already present (so that `insert` can avoid duplicates),
Lean needs to be able to **decide equality** on `α`. This is the
type class `DecidableEq α`.

## What happens without `DecidableEq`

Consider a type with no `DecidableEq` instance:

```
inductive Mystery where
  | a
  | b
```

If you tried to write `({Mystery.a} : Finset Mystery)`, Lean would produce
an error:

```
failed to synthesize instance
  DecidableEq Mystery
```

Lean refuses to build the finset because it cannot check for duplicates.
The fix is `deriving DecidableEq` in the type definition:

```
inductive Mystery where
  | a
  | b
deriving DecidableEq
```

## Your task

Below we define `Color` with `deriving DecidableEq`. Prove that
`insert Color.red {Color.blue}` equals `{Color.red, Color.blue}`
as finsets.

This is a definitional equality (both sides desugar to
`insert Color.red (insert Color.blue ∅)`), so `rfl` works.
The key point: **this only compiles because `Color` has `DecidableEq`**.
Without it, even writing `{Color.blue}` would fail.
"

inductive Color where
  | red
  | green
  | blue
deriving DecidableEq, Repr

/-- Inserting `Color.red` into `{Color.blue}` gives `{Color.red, Color.blue}`. -/
Statement : insert Color.red ({Color.blue} : Finset Color) = {Color.red, Color.blue} := by
  Hint "Both sides are the same expression after notation desugaring.
  The right-hand side desugars to `insert Color.red (insert Color.blue ∅)`,
  and the left side is `insert Color.red` applied to the singleton
  `insert Color.blue ∅`.
  What tactic proves definitional equalities?"
  Hint (hidden := true) "Try `rfl`. Both sides desugar to the same expression.

  **Remember**: this only works because `Color` has `DecidableEq`. Without it,
  Lean could not even build the singleton finset of `Color` values."
  rfl

Conclusion
"
This worked because `Color` has a `DecidableEq` instance. When we wrote
`deriving DecidableEq` in the definition of `Color`, Lean automatically
generated a function that can compare any two `Color` values for equality.

## What would fail without `DecidableEq`

If we had defined `Color` without `deriving DecidableEq`:

```
inductive Color where
  | red | green | blue
-- no deriving DecidableEq!
```

Then writing `({Color.blue} : Finset Color)` would give:

```
failed to synthesize instance
  DecidableEq Color
```

The `insert` operation cannot function without the ability to check
whether an element is already present.

## Why this matters

For all the types you will encounter in this course -- `Nat`, `Int`,
`Fin n`, `Bool`, product types, etc. -- `DecidableEq` is available
automatically. But when you define your own types, you need to either
derive it or provide it manually.

## The connection to `Multiset`

Recall that a `Finset α` is a pair: a `Multiset α` together with a proof
of `Nodup`. The `DecidableEq` instance is needed not for the multiset
itself, but for the operations that **maintain** the no-duplicates
invariant. Without it, `insert` cannot check whether the element is
already present.

**In plain language**: \"To build a finite set, you need to be able to
check whether two elements are equal. For natural numbers and most
concrete types, this is automatic. For abstract types, you must ensure
the capability exists.\"
"

/-- `DecidableEq α` is a type class asserting that equality on `α` is
algorithmically decidable: for any `a b : α`, we can compute whether
`a = b` or `a ≠ b`.

Most concrete types (`Nat`, `Int`, `Fin n`, `Bool`, etc.) have
`DecidableEq` instances automatically. For custom inductive types,
use `deriving DecidableEq`.

`DecidableEq` is required by `Finset` operations like `insert` and
membership (`∈`), because checking for duplicates requires comparing
elements.

## What happens without it

If you try to build a singleton finset for a type `α` without
`DecidableEq`, Lean produces:

```
failed to synthesize instance
  DecidableEq α
```

Fix: add `deriving DecidableEq` to your inductive type definition. -/
DefinitionDoc DecidableEq as "DecidableEq"

NewDefinition DecidableEq
DisabledTactic trivial decide native_decide simp aesop simp_all
