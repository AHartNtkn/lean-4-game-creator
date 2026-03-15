import GameServer.Commands
import Mathlib

World "ThreeFiniteness"
Level 5

Title "When to use which"

Introduction
"
# The Two `toFinset` Functions Agree

In Level 4 you met `Set.Finite.toFinset`, which converts a `Set.Finite`
proof into a finset. Mathlib also has `Set.toFinset`, which converts a
set into a finset using a `Fintype` instance on the subtype.

When *both* are available — when you have both a `Set.Finite` proof `h`
and a `Fintype` instance on `↑s` — they produce the same finset:

```
Set.Finite.toFinset_eq_toFinset :
  [Fintype ↑s] → (h : s.Finite) → h.toFinset = s.toFinset
```

## The full bridge: `Set.toFinset_univ`

For the universal set of a `Fintype`, there is a direct connection to
`Finset.univ`:

```
Set.toFinset_univ : (Set.univ : Set α).toFinset = Finset.univ
```

Combining these two lemmas lets you connect all three notions:
`Set.Finite` → `Set.Finite.toFinset` → `Set.toFinset` → `Finset.univ`.

## Your task

Prove that `Set.finite_univ.toFinset` for `Bool` equals `Finset.univ`.

This requires two rewrites:
1. `Set.Finite.toFinset_eq_toFinset` — switch from `h.toFinset` to `Set.toFinset`.
2. `Set.toFinset_univ` — connect `Set.univ.toFinset` to `Finset.univ`.
"

/-- The finset from `Set.finite_univ` for `Bool` equals `Finset.univ`. -/
Statement : (Set.finite_univ (α := Bool)).toFinset = (Finset.univ : Finset Bool) := by
  Hint "Start by rewriting `Set.finite_univ.toFinset` to `Set.univ.toFinset`
  using `Set.Finite.toFinset_eq_toFinset`.
  Try `rw [Set.Finite.toFinset_eq_toFinset]`."
  rw [Set.Finite.toFinset_eq_toFinset]
  Hint "The goal is now `(Set.univ : Set Bool).toFinset = Finset.univ`.
  Use `Set.toFinset_univ` to close it.
  Try `rw [Set.toFinset_univ]` or `exact Set.toFinset_univ`."
  Hint (hidden := true) "Use `exact Set.toFinset_univ`."
  exact Set.toFinset_univ

Conclusion
"
You connected all three notions in a single proof:

```
Set.finite_univ ──toFinset──▶ Set.Finite.toFinset
       │                            │
       │                  toFinset_eq_toFinset
       │                            │
       │                     Set.toFinset
       │                            │
       │                    toFinset_univ
       │                            │
       ▼                            ▼
  Set.Finite                  Finset.univ
```

## When to use which: a practical guide

| You need... | Use... | Why |
|---|---|---|
| To *state* a set is finite | `Set.Finite s` | Lightweight, no data needed |
| To *compute* with all elements of a type | `Fintype α` + `Finset.univ` | Gives enumeration |
| To *build* a specific finite collection | `Finset α` | Concrete, computable |
| To convert `Set.Finite` to a finset | `h.toFinset` | Extracts data from proof |
| To convert `Fintype` to a set-finiteness proof | `Set.finite_univ` | `Fintype` implies `Set.Finite` |

## The hierarchy

`Finset` is the most concrete (you have the data). `Fintype` is intermediate
(you have data for the whole type). `Set.Finite` is the most abstract
(you only know finiteness holds).

**In plain language**: \"Use `Set.Finite` when you only need to assert
finiteness. Use `Fintype` when you need to enumerate all elements of a
type. Use `Finset` when you need a concrete collection to compute with.\"
"

/-- `Set.Finite.toFinset_eq_toFinset` states that when both `h.toFinset`
and `s.toFinset` are defined (i.e., when `s` has both a `Set.Finite` proof
and a `Fintype` instance on `↑s`), they produce the same finset.

**Type**: `Set.Finite.toFinset_eq_toFinset : [Fintype ↑s] →
  (h : s.Finite) → h.toFinset = s.toFinset`

**When to use**: To switch between the two `toFinset` functions. -/
TheoremDoc Set.Finite.toFinset_eq_toFinset as "Set.Finite.toFinset_eq_toFinset" in "Set"

/-- `Set.toFinset_univ` connects `Set.toFinset` applied to `Set.univ` with
`Finset.univ`:

**Type**: `Set.toFinset_univ : (Set.univ : Set α).toFinset = Finset.univ`

This requires `[Fintype α]` and `[Fintype ↑Set.univ]`. -/
TheoremDoc Set.toFinset_univ as "Set.toFinset_univ" in "Set"

NewTheorem Set.Finite.toFinset_eq_toFinset Set.toFinset_univ
DisabledTactic trivial decide native_decide simp aesop simp_all
