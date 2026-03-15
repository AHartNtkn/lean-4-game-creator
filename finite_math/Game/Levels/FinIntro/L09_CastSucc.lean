import GameServer.Commands
import Mathlib

World "FinIntro"
Level 9

Title "Fin.castSucc -- embedding into a larger type"

Introduction
"
# `Fin.castSucc` -- the value stays, the type grows

`Fin.castSucc : Fin n → Fin (n + 1)` takes an element of `Fin n` and
views it as an element of `Fin (n + 1)`. The value stays the same --
it just becomes valid in a larger type.

For example, if `i : Fin 4` with `i.val = 2`, then
`Fin.castSucc i : Fin 5` also has `.val = 2`.

## The partition of `Fin (n + 1)`

Together, `Fin.castSucc` and `Fin.last` account for every element of
`Fin (n + 1)`:

```
Fin 4:     0   1   2   3
           ↓   ↓   ↓   ↓     ← castSucc
Fin 5:     0   1   2   3   4
                           ↑
                       Fin.last 4
```

Every element of `Fin (n + 1)` is either in the image of `Fin.castSucc`
(values `0, ..., n - 1`) or is `Fin.last n` (value `n`). This partition
will be fundamental when you do induction on `Fin`-indexed structures in
later worlds.

## Your task

Given `i : Fin 4`, prove that `(Fin.castSucc i).val < 4`.

The key is that `Fin.castSucc` preserves the underlying value:
`(Fin.castSucc i).val` is definitionally equal to `i.val`. So the goal
is really asking you to show `i.val < 4` -- which is exactly `i.isLt`,
the bound proof bundled inside `i`.

The lemma `Fin.val_castSucc` states `(Fin.castSucc i).val = i.val`.
"

/-- The value of `Fin.castSucc i` is still bounded by the original type's size. -/
Statement (i : Fin 4) : (Fin.castSucc i).val < 4 := by
  Hint "Since `(Fin.castSucc i).val` is definitionally `i.val`, the goal is
  really `i.val < 4`. What do you already know about `i`? Try `exact i.isLt`."
  exact i.isLt

Conclusion
"
`Fin.castSucc` is a pure type-level operation -- it changes which `Fin` type
the element belongs to, but leaves the numerical value untouched. This is
like saying \"the number 2 is less than 4, and *a fortiori* less than 5.\"

Since `(Fin.castSucc i).val = i.val` by definition, the bound `i.val < n`
still holds. You used `i.isLt` from Level 2 to close this -- your first
example of combining a new definition (`castSucc`) with a previously
learned fact (`.isLt`).

The key structural fact about `Fin (n + 1)`:
- Every element with value `< n` is in the image of `Fin.castSucc`
- The unique element with value `= n` is `Fin.last n`

This means `Fin.castSucc i ≠ Fin.last n` for any `i : Fin n` -- the image
of `castSucc` and the point `last` are disjoint. You will prove this
in the boss level.
"

/-- `Fin.castSucc : Fin n → Fin (n + 1)` embeds `Fin n` into `Fin (n + 1)` by
keeping the same value. If `i : Fin n`, then `(Fin.castSucc i).val = i.val`.
The element moves to a larger type without changing its numerical value. -/
DefinitionDoc Fin.castSucc as "Fin.castSucc"

NewDefinition Fin.castSucc
