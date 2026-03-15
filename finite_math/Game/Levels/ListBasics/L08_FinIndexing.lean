import GameServer.Commands
import Mathlib

World "ListBasics"
Level 8

Title "Indexing with Fin"

Introduction
"
# Accessing elements by position

You learned about `Fin n` in the first world -- it represents the natural
numbers `0, 1, ..., n-1`. Lists and `Fin` have a natural connection:
to access the element at position `i` in a list `l`, you need `i : Fin l.length`.

The function `List.get l i` returns the element at index `i`:
```
List.get (l : List α) (i : Fin l.length) : α
```

The type of `i` is `Fin l.length` -- this **guarantees** the index is
in bounds. There is no possibility of an out-of-bounds error because
the type system prevents it.

## Your task

The list `[10, 20, 30]` has length 3, so its valid indices are `Fin 3`,
i.e., `{0, 1, 2}`. The element at index 1 is `20`.

Prove that `[10, 20, 30].get ⟨1, by norm_num⟩ = 20`.

The angle-bracket `⟨1, by norm_num⟩` constructs an element of `Fin 3` --
the number `1` together with a proof that `1 < 3`. You used this
pattern in World 1! Here we use `norm_num` instead of `omega` because
the list length needs to be computed first.

This is a definitional equality, so `rfl` works.
"

/-- The element at index 1 of `[10, 20, 30]` is `20`. -/
Statement : [10, 20, 30].get ⟨1, by norm_num⟩ = 20 := by
  Hint "The function `List.get` on a concrete list with a concrete index
  evaluates to the element at that position. This is definitional. Try `rfl`."
  rfl

DisabledTactic decide native_decide aesop

Conclusion
"
You accessed the second element (index 1) of `[10, 20, 30]` and verified
it equals `20`. The key idea is that `List.get` takes a `Fin l.length`
argument, which **proves at the type level** that the index is valid.

This is where `Fin` from World 1 pays off: `Fin n` is not just an
abstract mathematical object. It is the **index type** for any structure
with `n` elements. Lists are the first concrete example, but later you
will see `Fin` used to index:
- rows and columns of matrices
- terms of a finite sum
- elements of `Finset.range n`

**Connection to `Fin`**: recall that `Fin n = { i : Nat // i < n }`.
When you write `⟨1, by norm_num⟩ : Fin 3`, you are providing the number
`1` together with a proof that `1 < 3`. The list accessor `List.get`
requires this proof, making out-of-bounds errors impossible.

**In plain language**: \"To access the $i$-th element of a list of length
$n$, you must prove that $i < n$. This is what `Fin n` enforces.\"
"

/-- `List.get l i` returns the element at index `i` in the list `l`, where
`i : Fin l.length`. The `Fin` type ensures the index is always in bounds.

Example: `[10, 20, 30].get ⟨1, by norm_num⟩ = 20`. -/
DefinitionDoc List.get as "List.get"

NewDefinition List.get
