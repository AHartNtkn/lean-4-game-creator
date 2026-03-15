import GameServer.Commands
import Mathlib

World "ListBasics"
Level 3

Title "List membership"

Introduction
"
# Proving membership symbolically

Given a list `l` and an element `a`, the proposition `a ∈ l` asserts that
`a` appears somewhere in `l`. For **concrete** lists like `[1, 2, 3]`, you
could verify membership with `decide`. But in this level, you will prove
membership **symbolically** -- for an arbitrary list.

## How membership unfolds

The membership relation for lists is defined recursively:
- `a ∈ []` is `False` (nothing is in the empty list)
- `a ∈ (b :: l)` is `a = b ∨ a ∈ l` (either `a` is the head, or `a` is in the tail)

The key rewriting lemma is `List.mem_cons`:
```
List.mem_cons : a ∈ b :: l ↔ a = b ∨ a ∈ l
```

## Your task

Prove that for any list `l`, the element `5` is in `5 :: l`.

Since `5` is the head of `5 :: l`, you know `5 = 5` holds.
You need to show `5 = 5 ∨ 5 ∈ l` -- and the left disjunct is true.

**Strategy**:
1. Use `rw [List.mem_cons]` to unfold the membership
2. Use `left` to choose the left disjunct
3. Close with `rfl`
"

/-- The head of a list is always a member of that list. -/
Statement (l : List Nat) : 5 ∈ 5 :: l := by
  Hint "The goal is `5 ∈ 5 :: l`. Unfold the membership with
  `rw [List.mem_cons]`."
  rw [List.mem_cons]
  Hint "Now the goal is `5 = 5 ∨ 5 ∈ l`. The left side is true.
  Use `left` to select the left disjunct."
  left
  Hint "Now prove `5 = 5` with `rfl`."
  rfl

DisabledTactic decide native_decide simp aesop

Conclusion
"
You proved membership by unfolding the definition: `a ∈ b :: l` means
`a = b ∨ a ∈ l`. Since we had `a = b` (both are `5`), we chose the left
disjunct and closed with `rfl`.

This is the symbolic version of what `decide` does automatically on
concrete lists. But the symbolic proof works for **any** list `l` --
you did not need to know what elements `l` contains.

The alternative approach uses `exact List.mem_cons_self 5 l`, which
directly states \"the head is always a member.\" Both approaches are
valid, but unfolding the definition teaches you how membership works.

**In plain language**: \"The first element of a list is always a member
of that list, regardless of what comes after it.\"
"

/-- `List.Mem a l` (written `a ∈ l`) asserts that `a` appears somewhere in the
list `l`. It is defined recursively:
- `a ∈ []` is `False`
- `a ∈ (b :: l)` is `a = b ∨ a ∈ l`

For concrete lists with decidable equality, `decide` can evaluate membership. -/
DefinitionDoc List.Mem as "List.Mem"

/-- `List.mem_cons a b l` states that `a ∈ b :: l ↔ a = b ∨ a ∈ l`.
This is the fundamental unfolding lemma for reasoning about list membership. -/
TheoremDoc List.mem_cons as "List.mem_cons" in "List"

/-- `left` selects the left side of a disjunction goal `P ∨ Q`, changing
the goal to `P`. -/
TacticDoc left

/-- `right` selects the right side of a disjunction goal `P ∨ Q`, changing
the goal to `Q`. -/
TacticDoc right

NewDefinition List.Mem
NewTheorem List.mem_cons
NewTactic left right
