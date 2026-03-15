import GameServer.Commands
import Mathlib

World "ListBasics"
Level 2

Title "Length of a cons"

Introduction
"
# Reasoning about `List.length`

Every list has a **length** -- the number of elements it contains.
The function `List.length` computes this recursively:

- `[].length = 0` (the empty list has no elements)
- `(a :: l).length = l.length + 1` (consing adds one to the length)

In this level, you will not just evaluate length on a concrete list.
Instead, you will prove a **symbolic** fact: given any list `l` of
natural numbers, `(0 :: l).length = l.length + 1`.

## The key lemma

The fact you need is `List.length_cons`:
```
List.length_cons (a : α) (l : List α) : (a :: l).length = l.length + 1
```

This is how `List.length` unfolds on a cons cell.

## Your task

Use `rw [List.length_cons]` to rewrite the left-hand side.
"

/-- Consing an element increases the length by one. -/
Statement (l : List Nat) : (0 :: l).length = l.length + 1 := by
  Hint "The goal is `(0 :: l).length = l.length + 1`. The lemma `List.length_cons`
  says exactly this: `(a :: l).length = l.length + 1`. Try `rw [List.length_cons]`."
  rw [List.length_cons]

DisabledTactic decide native_decide simp aesop

Conclusion
"
You used `rw [List.length_cons]` to unfold the definition of length on a
cons cell. After the rewrite, the goal became `l.length + 1 = l.length + 1`,
which Lean closed automatically.

This is a proof **about all lists** -- not just about `[1, 2, 3]`. The variable
`l` can be any list of natural numbers. This kind of symbolic reasoning is
what makes list proofs useful: you learn facts that apply to every list, not
just to specific examples.

Key fact: **length counts with duplicates**. The list `[1, 1, 1]` has
length 3, even though it contains only one distinct value. This will
matter later when we compare lists to finsets, which remove duplicates.

**In plain language**: \"Prepending an element to a list increases its length by one.\"
"

/-- `List.length l` returns the number of elements in the list `l`.
- `[].length = 0`
- `(a :: l).length = l.length + 1`

Length counts all elements including duplicates. -/
DefinitionDoc List.length as "List.length"

/-- `List.length_cons a l` states that `(a :: l).length = l.length + 1`.
This is the fundamental unfolding lemma for reasoning about list lengths. -/
TheoremDoc List.length_cons as "List.length_cons" in "List"

NewDefinition List.length
NewTheorem List.length_cons
