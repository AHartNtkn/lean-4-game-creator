import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 5

Title "Finsupp vs partial functions"

Introduction
"
# `Finsupp` Is a Total Function

A common misconception is that a finitely supported function is a
**partial function** — defined only at the points in its support.

This is wrong. A `Finsupp` `f : α →₀ M` is a **total function**:
`f a` is defined for *every* `a : α`. The support is merely the
set of points where `f a ≠ 0`. Outside the support, `f` returns `0`
— it does not fail to return a value.

## Concretizing the point

Consider `Finsupp.single 5 10 : ℕ →₀ ℕ`. Its support is `{5}`.
But what happens when you evaluate it at `999`? It returns `0`:

```
(Finsupp.single 5 10) 999 = 0
```

The function is defined at `999`. It just happens to be zero there.

## Partial functions vs `Finsupp`

If you wanted a *truly* partial function in Lean, you would use
`α → Option M` or `α →. M` (the type of partial functions). A
partial function at an undefined point returns `none`, not `0`.

A `Finsupp` is more like a function that \"defaults to zero.\"

## Your task

Prove two things about `Finsupp.single 5 10`:
1. It is defined at `999` and returns `0`.
2. `999` is not in its support.

The first part uses `single_apply` + `if_neg`. The second requires
showing that membership in the support implies nonzero value
(via `mem_support_iff`), which contradicts the value being `0`.
"

/-- `Finsupp.single 5 10` sends `999` to `0`, and `999` is not in its support. -/
Statement : (Finsupp.single 5 (10 : ℕ)) 999 = 0 ∧
    999 ∉ (Finsupp.single 5 (10 : ℕ)).support := by
  Hint "Use `constructor` to split into two goals."
  constructor
  · Hint "For the first goal, evaluate `single 5 10` at `999`.
    Use `rw [Finsupp.single_apply, if_neg (by omega)]`."
    Hint (hidden := true) "Try `rw [Finsupp.single_apply, if_neg (by omega)]`."
    rw [Finsupp.single_apply, if_neg (by omega)]
  · Hint "For the second goal, you need to show `999 ∉ (single 5 10).support`.

    Introduce the assumption that `999` is in the support using `intro h`,
    then use `rw [Finsupp.mem_support_iff] at h` to convert this to
    `(single 5 10) 999 ≠ 0`."
    intro h
    Hint "Now use `rw [Finsupp.mem_support_iff] at h` to convert the
    support membership to a statement about the value being nonzero."
    rw [Finsupp.mem_support_iff] at h
    Hint "The hypothesis `h` says `(single 5 10) 999 ≠ 0`.
    But we know `(single 5 10) 999 = 0` by evaluation!

    Rewrite with `single_apply` and `if_neg` inside `h`:
    `rw [Finsupp.single_apply, if_neg (by omega)] at h`."
    Hint (hidden := true) "Try `rw [Finsupp.single_apply, if_neg (by omega)] at h`."
    rw [Finsupp.single_apply, if_neg (by omega)] at h
    Hint "Now `h : 0 ≠ 0`, which is absurd. Close with `exact h rfl`."
    Hint (hidden := true) "Try `exact h rfl`."
    exact h rfl

Conclusion
"
You proved that a `Finsupp` is defined *everywhere*, even outside its
support — and that being outside the support simply means the value is `0`.

## The totality principle

| Concept | Finsupp | Partial function |
|---------|---------|------------------|
| Type | `α →₀ M` | `α →. M` or `α → Option M` |
| At a supported point | returns the value | returns `some value` |
| Outside the support | returns `0` | returns `none` |
| Total? | Yes | No |

A `Finsupp` is always total. The name \"finitely supported\" refers to
the *support being finite*, not to the function being partial.

## The proof pattern for `∉ support`

To prove `a ∉ f.support`, assume `a ∈ f.support`, rewrite with
`mem_support_iff` to get `f a ≠ 0`, then show `f a = 0` to get a
contradiction.

**In plain language**: \"Outside its support, a Finsupp is zero —
not undefined. It is a total function that happens to be zero almost
everywhere.\"
"

TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
