import GameServer.Commands
import Mathlib

World "FinsetConstructors"
Level 4

Title "Desugaring the {a, b, c} notation"

Introduction
"
# How `{1, 2, 3}` really works

In the last level, you saw that `{1, 2}` desugars to `insert 1 {2}`. Now
let us see the full picture with three elements.

## The desugaring chain

```
{1, 2, 3} = insert 1 (insert 2 (insert 3 ∅))
          = insert 1 (insert 2 {3})
```

Reading right-to-left:
1. Start with `∅`
2. Insert `3` to get `{3}`
3. Insert `2` to get `{2, 3}`
4. Insert `1` to get `{1, 2, 3}`

The outermost element in the notation is the **first** `insert`.

## Your task

Prove that `{1, 2, 3}` equals `insert 1 (insert 2 {3})` as a finset.

This exercises the notation desugaring: you need to see that both sides
are the same expression.
"

/-- The finset `{1, 2, 3}` equals `insert 1 (insert 2 {3})`. -/
Statement : ({1, 2, 3} : Finset Nat) = insert 1 (insert 2 {3}) := by
  Hint "Both sides of this equation are the same expression after
  notation desugaring. The curly-brace notation desugars to nested
  `insert` calls, and the singleton also desugars to an `insert`.
  So both sides are definitionally equal."
  Hint (hidden := true) "Try `rfl`. Both sides desugar to
  `insert 1 (insert 2 (insert 3 ∅))`."
  rfl

Conclusion
"
The curly-brace notation `{a, b, c}` is convenient, but it is important
to know what it hides. When you see `{1, 2, 3}` in a goal state, you are
looking at `insert 1 (insert 2 (insert 3 ∅))`.

This matters because:
- **Lemmas about `insert`** apply to literal finsets. When you need to
  prove `x ∈ {1, 2, 3}`, you are proving `x ∈ insert 1 (insert 2 {3})`,
  which `Finset.mem_insert` can handle.
- **Order in notation**: `{1, 2, 3}` inserts `1` first (outermost),
  then `2`, then `3` (innermost). But finsets have no order, so
  `{1, 2, 3} = {3, 1, 2}`.

## A preview of what is coming

In later worlds, you will use `Finset.mem_insert` to prove membership:
```
Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s
```
This recursive peeling -- \"either `a` is the element just inserted,
or `a` was already in the smaller finset\" -- is the key proof move
for membership in literal finsets.

**In plain language**: \"Writing $\\{1, 2, 3\\}$ means: start with nothing,
add 3, add 2, add 1. The result is a set, so the order does not matter.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
