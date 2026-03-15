import GameServer.Commands
import Mathlib

World "ListBasics"
Level 9

Title "No duplicates"

Introduction
"
# Lists with no repeated elements

The property `List.Nodup l` asserts that every element of `l` appears
exactly once -- the list has **no duplicates**.

For example:
- `[1, 2, 3].Nodup` is true (all elements are distinct)
- `[1, 2, 1].Nodup` is false (`1` appears twice)

## Why this matters

The distinction between lists with and without duplicates is at the heart
of the **List → Multiset → Finset** hierarchy that structures this course:

- A **list** has order and may have duplicates: `[1, 2, 1, 3]`
- A **multiset** forgets order but keeps duplicates: `{1, 1, 2, 3}`
- A **finset** forgets order and removes duplicates: `{1, 2, 3}`

`List.Nodup` is the exact condition under which a list can be converted
to a finset **without losing information about which elements are present**.

## The key lemma

For concrete lists, `List.nodup_cons` is the workhorse:
```
List.nodup_cons : (a :: l).Nodup ↔ a ∉ l ∧ l.Nodup
```

A cons-list has no duplicates if and only if the head does not appear in
the tail **and** the tail itself has no duplicates.

## The `simp` tactic

After unfolding `Nodup`, you will encounter goals like `1 ∉ [2, 3]`.
These non-membership goals involve checking a concrete value against
each element of a concrete list -- a tedious but mechanical task.

The `simp` tactic can close such goals automatically. It applies a
library of pre-proved simplification lemmas to reduce the goal until
it is solved. Think of `simp` as a calculator for \"obvious\" facts
about concrete data.

We introduce `simp` here specifically for these concrete membership
checks. You will see `simp` used in much greater depth in later courses.

## Your task

Prove two things:
1. The list `[1, 2, 3]` has no duplicates
2. The element `1` **is** in the list `[2, 1]`

The second part demonstrates exactly what prevents `[1, 2, 1]` from
being `Nodup`: unfolding `List.nodup_cons` on `1 :: [2, 1]` would require
`1 ∉ [2, 1]`, but `1 ∈ [2, 1]` -- so the proof would be blocked.

**Strategy for part 1**:
1. `constructor` to split the conjunction
2. `rw [List.nodup_cons]` to unfold the outermost cons
3. `constructor` to split into non-membership and tail-Nodup
4. `simp` to close the non-membership goal
5. Repeat for the inner cons cells
6. `exact List.nodup_nil` for the base case

**Strategy for part 2**:
Use `rw [List.mem_cons]` and `right`/`left` to navigate membership,
finishing with `rfl`.
"

/-- The list `[1, 2, 3]` has no duplicates, and `1 ∈ [2, 1]`. -/
Statement : ([1, 2, 3] : List Nat).Nodup ∧ (1 : Nat) ∈ [2, 1] := by
  Hint "The goal is a conjunction. Split it with `constructor`."
  constructor
  · Hint "First, prove `[1, 2, 3].Nodup`. Unfold the `Nodup` property
    on the outermost cons with `rw [List.nodup_cons]`."
    rw [List.nodup_cons]
    Hint "The goal is now `1 ∉ [2, 3] ∧ [2, 3].Nodup`. Split it with
    `constructor`."
    constructor
    · Hint "The goal is `1 ∉ [2, 3]`. This is a non-membership check on
      concrete values -- exactly the kind of \"obvious\" fact that `simp`
      handles. Try `simp`."
      simp
    · Hint "The goal is `[2, 3].Nodup`. Unfold again with
      `rw [List.nodup_cons]` and repeat the process."
      rw [List.nodup_cons]
      constructor
      · simp
      · Hint "The goal is `[3].Nodup`. One more unfolding:
        `rw [List.nodup_cons]`."
        rw [List.nodup_cons]
        constructor
        · simp
        · Hint "The goal is `[].Nodup`. The empty list trivially has
          no duplicates. Try `exact List.nodup_nil`."
          exact List.nodup_nil
  · Hint "Now prove that `1 ∈ [2, 1]`. This is the membership check
    that would **block** a `Nodup` proof for `[1, 2, 1]`.
    Unfold with `rw [List.mem_cons]`."
    rw [List.mem_cons]
    Hint "The goal is `1 = 2 ∨ 1 ∈ [1]`. Since `1 ≠ 2`, take the
    right branch with `right`."
    right
    Hint "The goal is `1 ∈ [1]`. Unfold again with `rw [List.mem_cons]`."
    rw [List.mem_cons]
    Hint "The goal is `1 = 1 ∨ 1 ∈ []`. Take the left branch with `left`."
    left
    Hint "The goal is `1 = 1`. Close with `rfl`."
    rfl

DisabledTactic decide native_decide norm_num simp_all aesop

Conclusion
"
You proved two things:
1. `[1, 2, 3].Nodup` -- every element appears exactly once
2. `1 ∈ [2, 1]` -- the number `1` is in the list `[2, 1]`

The second fact reveals **why** the list `[1, 2, 1]` fails `Nodup`.
When you unfold `List.nodup_cons` on `1 :: [2, 1]`, the first condition
requires `1 ∉ [2, 1]`. But you just proved `1 ∈ [2, 1]`, so that
condition is false. The `Nodup` proof is blocked at the very first step.

**Key concepts**:
- `List.Nodup` is defined recursively: each head must be fresh (not in
  the tail), and the tail must itself have no duplicates
- `List.nodup_cons` unfolds one layer: `(a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`
- `List.nodup_nil` is the base case: `[].Nodup`
- `simp` closes \"obvious\" goals about concrete data, such as `1 ∉ [2, 3]`

**In plain language**: A list has no duplicates when every element appears
at most once. To verify this, check each element against those that follow.
If any element reappears later, `Nodup` fails.

The `Nodup` property is the key bridge between lists and finsets: a list
satisfying `Nodup` can be converted to a `Finset` without losing information
about which elements are present.
"

/-- `List.Nodup l` asserts that every element of `l` appears at most once.
It is defined recursively:
- `[].Nodup` is always true
- `(a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`

`Nodup` is the bridge between lists and finsets: a list satisfying `Nodup`
can be converted to a finset without information loss. -/
DefinitionDoc List.Nodup as "List.Nodup"

/-- `List.nodup_cons` states that `(a :: l).Nodup ↔ a ∉ l ∧ l.Nodup`.
A cons-list has no duplicates iff the head is not in the tail and the
tail itself has no duplicates. -/
TheoremDoc List.nodup_cons as "List.nodup_cons" in "List"

/-- `List.nodup_nil` states that `[].Nodup`. The empty list trivially
has no duplicate elements. -/
TheoremDoc List.nodup_nil as "List.nodup_nil" in "List"

/-- `simp` is a powerful tactic that simplifies the goal using a database
of lemmas. It can evaluate concrete computations, unfold definitions,
and apply known simplification rules. Use `simp [lemma₁, lemma₂]` to
add specific lemmas to the simplification set. -/
TacticDoc simp

NewDefinition List.Nodup
NewTheorem List.nodup_cons List.nodup_nil
NewTactic simp
