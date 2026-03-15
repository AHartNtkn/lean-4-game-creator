import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 3

Title "Building finsets with insert"

Introduction
"
# `Finset.insert`: adding elements

You can grow a finset by inserting elements into it. The operation
`insert a s` produces a new finset that contains `a` and everything
in `s`.

## How `insert` works

```
insert a s = {a} ∪ s
```

If `a` is already in `s`, then `insert a s = s` -- inserting a duplicate
has no effect. (You will see this idempotency property in a later world.)

## Building `{1, 2}` step by step

The finset `{1, 2}` is built as:
```
{1, 2} = insert 1 {2} = insert 1 (insert 2 ∅)
```

Starting from `∅`, we insert `2` to get `{2}`, then insert `1` to get `{1, 2}`.

## Your task

Prove that `insert 1 {2}` equals `{1, 2}` as finsets of natural numbers.

The key insight is that `{1, 2}` is **notation** that Lean desugars to
`insert 1 (insert 2 ∅)`. Since `{2}` is `insert 2 ∅`, we have
`insert 1 {2} = insert 1 (insert 2 ∅) = {1, 2}`. This is definitional.
"

/-- `insert 1 {2}` equals `{1, 2}` as a finset. -/
Statement : insert 1 ({2} : Finset Nat) = {1, 2} := by
  Hint "The curly-brace notation desugars to nested `insert` calls.
  The right-hand side is `insert 1 (insert 2 ∅)`, and the left-hand
  side is `insert 1 (insert 2 ∅)`. Both sides are definitionally equal."
  Hint (hidden := true) "Try `rfl`. The notation desugars both sides
  to the same expression."
  rfl

Conclusion
"
You just saw the fundamental construction mechanism for finsets: **insert**.
Every literal finset `{a, b, c, ...}` is built by nesting `insert` calls:

```
{a, b, c} = insert a (insert b (insert c ∅))
```

This desugaring happens automatically -- when you write `{1, 2, 3}`, Lean
translates it to nested inserts behind the scenes. Understanding this
translation is important for two reasons:

1. **Proof strategy**: When you need to prove something about `{1, 2, 3}`,
   you are really proving something about `insert 1 (insert 2 {3})`.
   Lemmas about `insert` become your tools.

2. **Reading goal states**: Sometimes Lean will display a finset in its
   desugared form (`insert a s`) rather than in notation form (`{a, ...}`).
   Knowing they are the same thing prevents confusion.

**In plain language**: \"To build a finite set, start with the empty set and
add elements one at a time. In Lean, this is what the `{a, b, c}` notation
does automatically.\"
"

/-- `insert a s` adds element `a` to finset `s`. If `a` is already in `s`,
the result is unchanged (`insert` is idempotent).

The notation `{a, b, c}` desugars to `insert a (insert b {c})`, which is
`insert a (insert b (insert c ∅))`.

Key lemmas:
- `Finset.mem_insert`: `x ∈ insert a s ↔ x = a ∨ x ∈ s`
- `Finset.insert_eq_of_mem`: if `a ∈ s` then `insert a s = s` -/
DefinitionDoc Finset.insert as "Finset.insert"

NewDefinition Finset.insert
DisabledTactic trivial decide native_decide simp aesop simp_all
