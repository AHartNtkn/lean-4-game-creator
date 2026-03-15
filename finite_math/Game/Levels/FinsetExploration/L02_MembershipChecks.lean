import GameServer.Commands
import Mathlib

World "FinsetExploration"
Level 2

Title "Membership checks"

Introduction
"
# Membership in {1, 2, 3, 4, 5}

In the Membership world, you learned to prove `a ∈ s` using
`Finset.mem_insert` and `Finset.mem_singleton`. Now let's practice on
our concrete finset.

## Membership and non-membership

Recall the key membership lemmas:

```
Finset.mem_insert : a ∈ insert b s ↔ a = b ∨ a ∈ s
Finset.mem_singleton : a ∈ {b} ↔ a = b
```

For membership: reduce `3 ∈ {1, 2, 3, 4, 5}` by peeling off `insert`s
until you match.

For **non-membership** (`6 ∉ {1, 2, 3, 4, 5}`): you need to show that
`6` is not equal to any element. The `simp` family with the membership
lemmas handles this automatically by checking each possibility.

## Your task

Prove two things:
1. `3 ∈ {1, 2, 3, 4, 5}`
2. `6 ∉ {1, 2, 3, 4, 5}`
"

/-- 3 belongs to {1,2,3,4,5} and 6 does not. -/
Statement : (3 : Nat) ∈ ({1, 2, 3, 4, 5} : Finset Nat) ∧
    (6 : Nat) ∉ ({1, 2, 3, 4, 5} : Finset Nat) := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "Prove that `3` belongs to the finset. Recall that it is
    `insert 1 (insert 2 (insert 3 (insert 4 ...)))`. So `3` appears
    as the element being inserted at the third step.

    You can use `simp` with the membership lemmas."
    Hint (hidden := true) "Use
    `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Prove that `6` is not in the finset. You need to show `6` is
    not equal to `1`, `2`, `3`, `4`, or `5`. Again, `simp` with the
    membership lemmas will handle this by checking each disjunct."
    Hint (hidden := true) "Use
    `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
Both goals yielded to the same approach:
`simp [Finset.mem_insert, Finset.mem_singleton]`.

For **membership**, `simp` unfolds the iterated inserts and finds the
matching element. For **non-membership**, `simp` checks all disjuncts
and finds that none matches.

## Membership as search

Under the hood, proving `3 ∈ {1, 2, 3, 4, 5}` amounts to:
```
3 = 1 ∨ 3 = 2 ∨ 3 = 3 ∨ 3 = 4 ∨ 3 = 5
```
The third disjunct is true (`3 = 3`). For non-membership of `6`:
```
¬(6 = 1 ∨ 6 = 2 ∨ 6 = 3 ∨ 6 = 4 ∨ 6 = 5)
```
All five equalities are false.

**In plain language**: \"3 is in the set {1, 2, 3, 4, 5} because it is
one of the listed elements. 6 is not in the set because it differs from
every listed element.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
