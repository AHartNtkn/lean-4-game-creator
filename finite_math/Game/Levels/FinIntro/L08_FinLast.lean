import GameServer.Commands
import Mathlib

World "FinIntro"
Level 8

Title "Fin.last -- the largest element"

Introduction
"
# `Fin.last n` -- the top of `Fin (n + 1)`

The function `Fin.last n : Fin (n + 1)` gives you the *largest* element
of `Fin (n + 1)`. Its value is `n`.

For example:
- `Fin.last 0 : Fin 1` has `.val = 0` (the only element)
- `Fin.last 2 : Fin 3` has `.val = 2`
- `Fin.last 4 : Fin 5` has `.val = 4`

The lemma `Fin.val_last` states: `(Fin.last n).val = n`.

## Your task

Prove that `(Fin.last 4).val = 4`.
"

/-- The value of `Fin.last n` is `n`. -/
Statement : (Fin.last 4).val = 4 := by
  Hint "This is true by definition. Try `rfl`."
  rfl

Conclusion
"
`Fin.last n` is defined to have `.val = n`, so this is definitionally true.

Here is the picture for `Fin 5`:
```
Elements:  0   1   2   3   4
                           ↑
                       Fin.last 4
```

Note that `Fin.last 4` lives in `Fin 5`, not `Fin 4`. The argument to
`Fin.last` is the *value*, not the type index. This means:
- `Fin.last 3` is the largest element of `Fin 4` (value 3, not 4)
- `Fin.last (n-1)` is the largest element of `Fin n`

This is a consequence of zero-indexing: the largest element of an `n`-element
set has index `n - 1`.
"

/-- `Fin.last n` is the largest element of `Fin (n + 1)`. It has value `n`.
For example, `Fin.last 4 : Fin 5` has `(Fin.last 4).val = 4`. -/
DefinitionDoc Fin.last as "Fin.last"

NewDefinition Fin.last
