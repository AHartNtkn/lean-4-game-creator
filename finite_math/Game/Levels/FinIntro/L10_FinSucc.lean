import GameServer.Commands
import Mathlib

World "FinIntro"
Level 10

Title "Fin.succ -- shifting up by one"

Introduction
"
# `Fin.succ` -- increment the value

`Fin.succ : Fin n → Fin (n + 1)` maps an element of `Fin n` into
`Fin (n + 1)` by adding 1 to its value.

Compare the three navigation functions:
- `Fin.castSucc i` keeps the value and widens the type: `val ↦ val`
- `Fin.succ i` increments the value and widens the type: `val ↦ val + 1`
- `Fin.last n` is the constant largest element with value `n`

For example, with `i : Fin 4` and `i.val = 1`:
- `(Fin.castSucc i).val = 1` (same value, type `Fin 5`)
- `(Fin.succ i).val = 2` (value + 1, type `Fin 5`)

## Your task

Prove that `(Fin.succ i).val = i.val + 1` for `i : Fin 4`.

The lemma `Fin.val_succ` states exactly this. It is also true by
definition, so `rfl` works.
"

/-- `Fin.succ` increments the value by 1. -/
Statement (i : Fin 4) : (Fin.succ i).val = i.val + 1 := by
  Hint "This is true by definition. Try `rfl`."
  rfl

Conclusion
"
`Fin.succ` is the natural partner to `Fin.castSucc`:

```
Fin 4:     0   1   2   3
           ↓   ↓   ↓   ↓     ← castSucc (same value)
Fin 5:     0   1   2   3   4
               ↑   ↑   ↑   ↑ ← succ (value + 1)
Fin 4:     0   1   2   3
```

Notice the overlap: `Fin.castSucc` maps to `{0, 1, 2, 3}` and `Fin.succ`
maps to `{1, 2, 3, 4}`. They agree on `{1, 2, 3}` but differ at the
endpoints.

The three functions `castSucc`, `succ`, and `last` are the building blocks
for navigating `Fin (n + 1)`. In later worlds, you will use them to:
- Split sums over `Fin (n + 1)` into a sum over `Fin n` plus a last term
- Define functions on `Fin (n + 1)` by cases
- Prove inductive properties of `Fin`-indexed sequences
"

/-- `Fin.succ : Fin n → Fin (n + 1)` maps an element into the next-larger
finite type by incrementing its value by 1.
If `i : Fin n`, then `(Fin.succ i).val = i.val + 1`. -/
DefinitionDoc Fin.succ as "Fin.succ"

NewDefinition Fin.succ
