import GameServer.Commands
import Mathlib

World "FinsetMembership"
Level 7

Title "Non-membership"

Introduction
"
# Proving an element is NOT in a finset

So far you have proved positive membership facts: `a ∈ s`. But it is
equally important to prove **non-membership**: `a ∉ s`.

## What `∉` means

The notation `a ∉ s` is defined as `¬(a ∈ s)`, which is `a ∈ s → False`.
To prove `a ∉ s`, you must show that assuming `a ∈ s` leads to a
contradiction.

## Manual approach

You could introduce the membership hypothesis with `intro h`, then
use `Finset.mem_insert` to break it into cases, and show each case
is contradictory (since `4 ≠ 1`, `4 ≠ 2`, `4 ≠ 3`).

## The `simp` approach

For concrete finsets with known elements, `simp` with membership lemmas
handles non-membership just as easily as membership:

```
simp [Finset.mem_insert, Finset.mem_singleton]
```

`simp` will expand the membership, evaluate all the equalities
(`4 = 1` is `False`, `4 = 2` is `False`, `4 = 3` is `False`), and
conclude that `4 ∈ {1, 2, 3}` is `False`.

## Your task

Prove that `4 ∉ ({1, 2, 3} : Finset Nat)`.
"

/-- `4` is not an element of `{1, 2, 3}`. -/
Statement : 4 ∉ ({1, 2, 3} : Finset Nat) := by
  Hint "The goal is a non-membership claim: `4` is not in the finset
  containing 1, 2, 3. Since all elements are concrete numbers, `simp`
  with the membership lemmas can verify that `4` does not equal any
  element of the finset."
  Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
  simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
`simp` proved non-membership by expanding the membership condition
into `4 = 1 ∨ 4 = 2 ∨ 4 = 3` and showing each disjunct is false.

## The manual alternative

If you wanted to prove this without `simp`, you could write:

```
intro h
rw [Finset.mem_insert] at h
rcases h with h1 | h
· omega          -- 4 = 1 is impossible
· rw [Finset.mem_insert] at h
  rcases h with h1 | h
  · omega        -- 4 = 2 is impossible
  · rw [Finset.mem_singleton] at h
    omega         -- 4 = 3 is impossible
```

This manual approach introduces the membership hypothesis, then
systematically eliminates each possibility. The `omega` tactic
closes impossible arithmetic equalities.

For concrete non-membership, `simp` is clearly better. But the
manual approach previews a technique you will use soon: **rewriting
a membership hypothesis** (not just a goal) with `rw [...] at h`.

**In plain language**: \"4 is not in {1, 2, 3} because 4 is not equal
to 1, not equal to 2, and not equal to 3. There are no other
possibilities.\"
"

DisabledTactic trivial decide native_decide aesop simp_all
