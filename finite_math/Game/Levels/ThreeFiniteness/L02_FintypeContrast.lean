import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 2

Title "Fintype: Type-level finiteness"

Introduction
"
# `Fintype` vs `Set.Finite`

In the previous level you saw `Set.Finite`, which says a *set* is finite.
Now recall `Fintype` from an earlier world: it says a *type* is finite.

## The difference

| | `Set.Finite s` | `Fintype α` |
|---|---|---|
| **Applies to** | a set `s : Set α` | a type `α` |
| **Nature** | a proposition (`Prop`) | a type class (carries data) |
| **Data** | none — just a proof | `Finset.univ` — all elements listed |
| **Example** | `{1,2,3}.Finite` | `Fintype (Fin 3)` |

## The bridge: `Set.finite_univ`

If `α` has a `Fintype` instance, then every element of `α` can be
enumerated. In particular, the set `Set.univ : Set α` (which contains
*all* elements of `α`) must be finite:

```
Set.finite_univ : [Finite α] → (Set.univ : Set α).Finite
```

This bridges the two notions: type-level finiteness (`Fintype`) implies
set-level finiteness (`Set.Finite`) for the universal set.

## Your task

Prove that `Set.univ` for `Bool` is finite. Since `Bool` has a `Fintype`
instance (there are only two values: `true` and `false`), the lemma
`Set.finite_univ` gives you the proof directly.
"

/-- The universal set of `Bool` is finite. -/
Statement : (Set.univ : Set Bool).Finite := by
  Hint "Since `Bool` is a finite type (it has a `Fintype` instance),
  the set of all `Bool` values is finite. Use `Set.finite_univ`."
  Hint (hidden := true) "Use `exact Set.finite_univ`."
  exact Set.finite_univ

Conclusion
"
You used `Set.finite_univ` to prove that the universal set of `Bool` is
finite. This works because `Bool` has a `Finite` instance (which follows
automatically from its `Fintype` instance).

## Why this matters

This conversion is one-directional in a natural sense:

- **`Fintype α` implies `Set.univ.Finite`**: if the type is finite,
  then certainly the set of all elements is finite.
- **`Set.univ.Finite` does NOT give you `Fintype α` for free**: knowing
  the set is finite (a `Prop`) does not hand you the enumeration data
  that `Fintype` carries.

In practice, `Fintype` is the stronger notion. When you have it, you
automatically get `Set.Finite` for `Set.univ` and for every subset.

**In plain language**: \"If a type is finite, then its universal set
is certainly finite. The converse requires more work.\"
"

/-- `Set.finite_univ` proves that the universal set `Set.univ` is finite
when the type has a `Finite` instance (which every `Fintype` provides).

**Type**: `Set.finite_univ : [Finite α] → (Set.univ : Set α).Finite`

**When to use**: When you have `Fintype α` (or `Finite α`) and need
to show `(Set.univ : Set α).Finite`. -/
TheoremDoc Set.finite_univ as "Set.finite_univ" in "Set"

NewTheorem Set.finite_univ
DisabledTactic trivial decide native_decide simp aesop simp_all
