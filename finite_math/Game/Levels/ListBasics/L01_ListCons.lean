import GameServer.Commands
import Mathlib

World "ListBasics"
Level 1

Title "The empty list and cons"

Introduction
"
# Welcome to Lists

In this world, you will learn about `List` -- Lean's built-in type for
finite ordered sequences. Lists are the most concrete data structure for
holding a collection of elements, and they are the foundation on which
multisets and finsets are built.

## How lists are constructed

A `List α` (a list of elements of type `α`) is built from two constructors:

1. `[]` -- the empty list (also called `List.nil`)
2. `a :: l` -- the list with head `a` followed by tail `l` (also called `List.cons a l`)

The notation `::` is called **cons** (short for \"construct\"). It prepends
a single element to the front of an existing list.

## List literal notation

Instead of writing `1 :: 2 :: 3 :: []`, Lean lets you write `[1, 2, 3]`.
This is just syntactic sugar -- the two expressions are definitionally equal.

## Your task

Prove that `[1, 2, 3]` equals `1 :: 2 :: 3 :: []`.

Since these are definitionally equal, `rfl` will work.
"

/-- The list `[1, 2, 3]` is the same as `1 :: 2 :: 3 :: []`. -/
Statement : [1, 2, 3] = (1 :: 2 :: 3 :: [] : List Nat) := by
  Hint "The list literal `[1, 2, 3]` is definitionally equal to `1 :: 2 :: 3 :: []`.
  Try `rfl`."
  rfl

Conclusion
"
The list notation `[1, 2, 3]` is shorthand for `1 :: (2 :: (3 :: []))`.
Every list is built by repeatedly prepending elements with `::` onto
the empty list `[]`.

Think of `::` as \"put this element on the front.\" The list `[1, 2, 3]`
was built by:
- starting with the empty list `[]`
- prepending `3` to get `[3]`
- prepending `2` to get `[2, 3]`
- prepending `1` to get `[1, 2, 3]`

**In plain language**: A list is a finite sequence of elements in a
specific order. The notation `[a, b, c]` means \"the sequence containing
$a$, then $b$, then $c$, in that order.\"

In the next level, you will learn how to reason about the length of a list.
"

/-- `List α` is the type of finite ordered sequences of elements of type `α`.
Lists are built from `[]` (the empty list) and `a :: l` (cons). The notation
`[a, b, c]` is shorthand for `a :: b :: c :: []`. -/
DefinitionDoc List as "List"

/-- `List.nil` (written `[]`) is the empty list. It contains no elements.
`[].length = 0` and `a ∉ []` for any `a`. -/
DefinitionDoc List.nil as "List.nil"

/-- `List.cons a l` (written `a :: l`) prepends element `a` to the front of
list `l`. For example, `1 :: [2, 3] = [1, 2, 3]`. -/
DefinitionDoc List.cons as "List.cons"

NewDefinition List List.nil List.cons
DisabledTactic decide native_decide aesop
