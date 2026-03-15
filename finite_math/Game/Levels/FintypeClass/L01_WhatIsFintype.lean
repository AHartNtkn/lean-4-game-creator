import GameServer.Commands
import Mathlib

World "FintypeClass"
Level 1

Title "What is Fintype?"

Introduction
"
# The `Fintype` Type Class

In earlier worlds you worked with `Finset α` --- a *specific* finite
collection of elements of `α`. But sometimes you want to say that
the type `α` **itself** is finite: that every element of `α` can be
listed in a single, universal finset.

## The definition

`Fintype α` is a type class with two fields:
```
class Fintype (α : Type) where
  elems : Finset α
  complete : ∀ x : α, x ∈ elems
```

An instance of `Fintype α` provides:
1. `elems` --- a finset that contains *every* element of `α`, and
2. `complete` --- a proof that every `x : α` belongs to `elems`.

The universal finset is accessed via `Finset.univ`: given
`[Fintype α]`, `Finset.univ : Finset α` is the finset of all elements.

## Your task

The type `Fin 3` has a `Fintype` instance (Lean provides one
automatically). Prove that `Finset.univ` for `Fin 3` has exactly 3
elements.

Since `Finset.univ` *is* the finset of all elements of `Fin 3`,
and `Fin 3` has exactly 3 elements, this is a definitional equality.
Try `rfl`.
"

/-- The universal finset of `Fin 3` has 3 elements. -/
Statement : (Finset.univ : Finset (Fin 3)).card = 3 := by
  Hint "Since `Finset.univ` for `Fin 3` contains `0, 1, 2` by definition,
  its cardinality is definitionally `3`. Try `rfl`."
  Hint (hidden := true) "Use `rfl`. The cardinality of `Finset.univ` for
  `Fin 3` is computed by Lean to be `3`."
  rfl

Conclusion
"
The universal finset of `Fin 3` is `{0, 1, 2}`, which has exactly 3 elements.
Lean computed this automatically because `Fin 3` has a `Fintype` instance,
meaning Lean knows how to enumerate *all* elements of the type.

## Key concept

`Finset.univ` is the bridge between type-level finiteness (`Fintype α`)
and the concrete finsets you have been working with. Every `Fintype`
instance equips the type with a `Finset.univ` that contains all elements.

**In plain language**: \"A fintype is a type where you can list all the
elements. The universal finset is that list.\"
"

/-- `Fintype α` is a type class asserting that `α` is finite. It provides a
finset `Finset.univ` containing every element of `α`, together with a proof
that every element belongs to it.

**Fields**:
- `elems : Finset α` — the universal finset
- `complete : ∀ x, x ∈ elems` — proof of universality

**Examples**:
- `Fin n` has a `Fintype` instance for every `n`.
- `Bool` has a `Fintype` instance (2 elements).
- `Nat` does **not** have a `Fintype` instance.

**When to use**: When a proof requires that all elements of a type can be
enumerated, or when you want to use `Finset.univ` or `Fintype.card`. -/
DefinitionDoc Fintype as "Fintype"

/-- `Finset.univ` is the finset containing *every* element of a type `α`,
provided `α` has a `Fintype` instance.

**Type**: `Finset.univ : Finset α` (requires `[Fintype α]`)

**Key property**: `Finset.mem_univ : ∀ x, x ∈ Finset.univ`

**When to use**: When you need to refer to "all elements" of a finite type
as a finset. -/
DefinitionDoc Finset.univ as "Finset.univ"

NewDefinition Fintype Finset.univ
DisabledTactic trivial decide native_decide aesop simp_all
