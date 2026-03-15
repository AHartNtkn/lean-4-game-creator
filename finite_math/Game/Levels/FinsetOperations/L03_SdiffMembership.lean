import GameServer.Commands
import Mathlib

World "FinsetOperations"
Level 3

Title "Set difference membership"

Introduction
"
# Finset difference: elements in one but not the other

The **set difference** `s \\ t` contains exactly the elements that belong
to `s` but **not** to `t`. The membership lemma is:

```
Finset.mem_sdiff : a ∈ s \\ t ↔ a ∈ s ∧ a ∉ t
```

Notice that this uses a conjunction with a **negation**: the element must
be in `s` **and** not in `t`.

## Notation

The backslash `\\` in `s \\ t` is the set-difference operator. (In Lean,
you type it as a single backslash character.)

## Your task

Given `s = {1, 2, 3}` and `t = {2, 3, 4}`, prove that `1 ∈ s \\ t`.

**Strategy**: Rewrite with `Finset.mem_sdiff`, split the conjunction,
prove `1 ∈ s`, then prove `1 ∉ t`.
"

/-- `1` belongs to `{1, 2, 3} \\ {2, 3, 4}`. -/
Statement : 1 ∈ ({1, 2, 3} : Finset Nat) \ {2, 3, 4} := by
  Hint "The goal asks whether `1` belongs to the set difference of
  the finsets containing 1, 2, 3 and 2, 3, 4. Rewrite with
  `Finset.mem_sdiff` to turn this into: `1` is in the first finset
  **and** `1` is not in the second finset."
  Hint (hidden := true) "Use `rw [Finset.mem_sdiff]`."
  rw [Finset.mem_sdiff]
  Hint "The goal is now a conjunction. Split it with `constructor`."
  Hint (hidden := true) "Use `constructor`."
  constructor
  · Hint "Prove that `1` belongs to the finset containing 1, 2, 3."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]
  · Hint "Prove that `1` does not belong to the finset containing 2, 3, 4.
    Recall that `∉` means membership implies `False`. The `simp` tactic
    can handle concrete non-membership."
    Hint (hidden := true) "Use `simp [Finset.mem_insert, Finset.mem_singleton]`."
    simp [Finset.mem_insert, Finset.mem_singleton]

Conclusion
"
You proved your first set-difference membership fact. The pattern is:

1. **Rewrite** with `Finset.mem_sdiff` to get a conjunction.
2. **Split** with `constructor`.
3. Prove **membership** in the first finset.
4. Prove **non-membership** in the second finset.

## Summary of the three operations

| Operation | Lemma | Logical form |
|-----------|-------|-------------|
| `s ∪ t` | `mem_union` | `a ∈ s ∨ a ∈ t` |
| `s ∩ t` | `mem_inter` | `a ∈ s ∧ a ∈ t` |
| `s \\ t` | `mem_sdiff` | `a ∈ s ∧ a ∉ t` |

Each operation has a membership lemma that reduces the question to
familiar logical connectives. This table is worth memorizing.

**In plain language**: \"1 is in {1, 2, 3} \\ {2, 3, 4} because
1 is in {1, 2, 3} and 1 is not in {2, 3, 4}.\"
"

/-- `Finset.mem_sdiff` states that `a ∈ s \\ t ↔ a ∈ s ∧ a ∉ t`.

An element belongs to the set difference `s \\ t` exactly when it
belongs to `s` and does not belong to `t`. Use `rw [Finset.mem_sdiff]`
to convert a set-difference membership goal into a conjunction. -/
TheoremDoc Finset.mem_sdiff as "Finset.mem_sdiff" in "Finset"

NewTheorem Finset.mem_sdiff
DisabledTactic trivial decide native_decide aesop simp_all
