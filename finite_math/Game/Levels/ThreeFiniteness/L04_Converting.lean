import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 4

Title "Converting: Set.Finite → Finset"

Introduction
"
# From `Set.Finite` to `Finset`

You have seen how to go *from* `Finset` or `Fintype` *to* `Set.Finite`.
Now you will go the other direction: from a `Set.Finite` proof to a
`Finset`.

## `Set.Finite.toFinset`

Given a proof `h : s.Finite`, the term `h.toFinset` is a `Finset α`
whose elements are exactly the elements of `s`:

```
Set.Finite.toFinset : s.Finite → Finset α
```

The membership characterization is:

```
Set.Finite.mem_toFinset : a ∈ h.toFinset ↔ a ∈ s
```

So `h.toFinset` is a finset that represents the same collection as the
set `s`, but as concrete data rather than a predicate.

## Your task

Given a proof `h` that `{1, 2} : Set Nat` is finite, prove that `1`
belongs to `h.toFinset`.

Strategy: rewrite with `Set.Finite.mem_toFinset` to translate the finset
membership into set membership, then prove `1 ∈ ({1, 2} : Set Nat)`.
"

/-- `1` belongs to the finset obtained from the finite set `{1, 2}`. -/
Statement (h : ({1, 2} : Set Nat).Finite) : 1 ∈ h.toFinset := by
  Hint "Use `rw [Set.Finite.mem_toFinset]` to convert the goal from
  `1 ∈ h.toFinset` to `1 ∈ insert 1 (singleton 2)`."
  rw [Set.Finite.mem_toFinset]
  Hint "The goal is now `1 ∈ insert 1 (singleton 2)` (i.e., `1` is in the
  set containing `1` and `2`). This holds because `1` is the inserted element.
  Use `exact Set.mem_insert 1 (singleton 2)` or equivalently `left; rfl`."
  Hint (hidden := true) "Use `exact Set.mem_insert 1 (singleton 2)`.
  Alternatively: `left` then `rfl`."
  exact Set.mem_insert 1 {2}

Conclusion
"
You converted a `Set.Finite` proof into a `Finset` using `h.toFinset`,
then used `Set.Finite.mem_toFinset` to reason about membership.

## The conversion pipeline

```
Set.Finite s ──toFinset──▶ Finset α
                              │
                         mem_toFinset
                              │
                     a ∈ h.toFinset ↔ a ∈ s
```

The key insight: `Set.Finite.toFinset` gives you a finset, and
`Set.Finite.mem_toFinset` lets you *reason about that finset* by
reasoning about the original set.

## A subtlety: `Set.Finite.toFinset` vs `Set.toFinset`

Mathlib has *two* functions that convert sets to finsets:

- `Set.Finite.toFinset` takes a proof `h : s.Finite`.
- `Set.toFinset` takes a `Fintype` instance on the subtype `↑s`.

They produce the same finset (as expressed by `Set.Finite.toFinset_eq_toFinset`),
but they are invoked differently. You will use this connection in Level 5.

**In plain language**: \"A `Set.Finite` proof is a certificate of finiteness.
`toFinset` cashes that certificate for a concrete finset.\"
"

/-- `Set.Finite.toFinset` converts a `Set.Finite` proof into a `Finset`
containing exactly the elements of the set.

**Type**: `Set.Finite.toFinset : s.Finite → Finset α`

**Key property**: `Set.Finite.mem_toFinset : a ∈ h.toFinset ↔ a ∈ s` -/
DefinitionDoc Set.Finite.toFinset as "Set.Finite.toFinset"

/-- `Set.Finite.mem_toFinset` characterizes membership in `h.toFinset`:
an element belongs to the finset if and only if it belongs to the
original set.

**Type**: `Set.Finite.mem_toFinset (hs : s.Finite) : a ∈ hs.toFinset ↔ a ∈ s`

**When to use**: After converting a `Set.Finite` proof to a finset via
`toFinset`, use this to translate finset membership back to set membership. -/
TheoremDoc Set.Finite.mem_toFinset as "Set.Finite.mem_toFinset" in "Set"

/-- `Set.mem_insert a s` proves that `a ∈ insert a s`. In set-builder
notation, `a ∈ {a} ∪ s`.

**Type**: `Set.mem_insert (a : α) (s : Set α) : a ∈ insert a s` -/
TheoremDoc Set.mem_insert as "Set.mem_insert" in "Set"

NewDefinition Set.Finite.toFinset
NewTheorem Set.Finite.mem_toFinset Set.mem_insert
DisabledTactic trivial decide native_decide simp aesop simp_all
