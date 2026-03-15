import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 8

Title "Case analysis on membership"

Introduction
"
# The `by_cases` tactic

Sometimes you need to reason about whether an element **is** or
**is not** in a finset, without knowing which. The `by_cases` tactic
splits the proof into two cases.

## Syntax

```
by_cases h : a ∈ s
```

This creates two goals:
- In the first, you have `h : a ∈ s` (the element is in the finset).
- In the second, you have `h : a ∉ s` (the element is not in the finset).

## Why this works

For finsets, membership is **decidable**: Lean can determine (in
principle) whether any element belongs to a finset. The `by_cases`
tactic exploits this decidability.

## Your task

Prove that for any finsets `s` and `t`, the set difference `s \\ t`
is a subset of `s`. In other words: removing elements never adds
new ones.

**Strategy**: Introduce `a` and `ha : a ∈ s \\ t`. Rewrite `ha` with
`mem_sdiff` to learn that `a ∈ s ∧ a ∉ t`. Extract the first
component.

Actually, for this level you do NOT need `by_cases` -- this is a
warm-up. But the next level will use it.

Wait -- let's make this level actually use `by_cases`. Here is a
better task:

Prove that `s ⊆ (s \\ t) ∪ t`. This says: every element of `s` is
either in the part of `s` outside `t`, or in `t` itself.

**Strategy**: Introduce `a` and `ha : a ∈ s`. Use `by_cases ht : a ∈ t`
to split on whether `a` is in `t`. If yes, take the right branch of
the union. If no, take the left branch and use `mem_sdiff`.
"

/-- Every element of `s` is in `(s \\ t) ∪ t`. -/
Statement (s t : Finset Nat) : s ⊆ (s \ t) ∪ t := by
  Hint "Introduce an arbitrary element `a` and its membership `ha`."
  Hint (hidden := true) "Use `intro a ha`."
  intro a ha
  Hint "You need to show `a ∈ (s \\ t) ∪ t`. The key question is
  whether `a ∈ t` or `a ∉ t`. Use `by_cases` to split on this."
  Hint (hidden := true) "Use `by_cases ht : a ∈ t`."
  by_cases ht : a ∈ t
  · Hint "**Case 1**: `ht : a ∈ t`. Since `a` is in `t`, it is in
    `(s \\ t) ∪ t` via the right side of the union."
    Hint (hidden := true) "Use `rw [Finset.mem_union]`, then `right`,
    then `exact ht`."
    rw [Finset.mem_union]
    right
    exact ht
  · Hint "**Case 2**: `ht : a ∉ t`. Since `a ∈ s` but `a ∉ t`,
    we have `a ∈ s \\ t`. So `a` is in `(s \\ t) ∪ t` via the left
    side."
    Hint (hidden := true) "Use `rw [Finset.mem_union]`, then `left`,
    then `rw [Finset.mem_sdiff]`, then `exact ⟨ha, ht⟩`."
    rw [Finset.mem_union]
    left
    rw [Finset.mem_sdiff]
    exact ⟨ha, ht⟩

Conclusion
"
You proved that `s ⊆ (s \\ t) ∪ t` -- every element of `s` is either
in `s \\ t` (the part outside `t`) or in `t` itself. This is a
partition-like fact.

## The `by_cases` pattern

The `by_cases` tactic is essential when you need to reason about
**whether** an element belongs to a finset:

```
by_cases h : a ∈ s
```

This gives you two goals:
- One where `h : a ∈ s` (positive case)
- One where `h : a ∉ s` (negative case)

## When to use `by_cases`

Use `by_cases` when:
- The goal involves set difference (which requires knowing membership
  in the subtracted set).
- You need to prove something \"by exhaustion\" on membership.
- Neither `left` nor `right` alone suffices -- you need to consider
  both possibilities.

This tactic will be essential in the distributivity and De Morgan
levels coming up.

**In plain language**: \"Given a ∈ s, either a ∈ t or a ∉ t. If a ∈ t,
then a is in the union via t. If a ∉ t, then a is in s \\ t, hence
in the union via s \\ t.\"
"

/-- `by_cases` performs case analysis on a decidable proposition.

`by_cases h : P` creates two goals: one where `h : P` and one where
`h : ¬P`. For finset membership, `by_cases h : a ∈ s` splits on
whether `a` is in `s` or not.

This is useful when you need to reason about membership in set
difference or when neither branch of a disjunction is immediately
available. -/
TacticDoc by_cases

NewTactic by_cases
DisabledTactic trivial decide native_decide aesop simp_all
