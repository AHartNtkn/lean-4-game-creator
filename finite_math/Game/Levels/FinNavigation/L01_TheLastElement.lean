import Game.Metadata

World "FinNavigation"
Level 1

Title "The Last Element"

Introduction "
# Fin.last: The Boundary Element

In the previous world, you learned that `Fin n` contains the numbers
$0, 1, \\ldots, n-1$. But how do you name the *largest* element?

For `Fin (n+1)`, the largest element has value `n`. Lean gives it a
name: **`Fin.last n`**.

`Fin.last n` lives in `Fin (n+1)` — not `Fin n` — because `n` is
less than `n+1` but not less than `n`.

The theorem **`Fin.val_last`** extracts its value:
$$\\texttt{(Fin.last } n\\texttt{).val} = n$$

**Your task**: Show that `Fin.last 4` has value `4`.
"

/-- `Fin.last 4` has value 4. -/
Statement : (Fin.last 4).val = 4 := by
  Hint "Use `exact Fin.val_last 4` to close this goal.
  (Since the definition is transparent, `rfl` also works here.
  But `Fin.val_last` is the general tool you'll need when `n`
  is a variable.)"
  exact Fin.val_last 4

Conclusion "
`Fin.val_last n` tells you that `(Fin.last n).val = n`.

This is the analog of saying: the largest element of
$\\{0, 1, \\ldots, n\\}$ is $n$. In Lean, you need `Fin.val_last`
to access this fact because `Fin.last` is an opaque term —
the type system doesn't automatically compute its value.

In the next level, you'll use `Fin.val_last` as a **rewrite** tool
inside a larger proof.
"

/-- `Fin.last n` is the largest element of `Fin (n + 1)`.
Its underlying value is `n`.

## Construction
`Fin.last n : Fin (n + 1)`

## Example
`Fin.last 4 : Fin 5` — the element with value 4.

## Value
`(Fin.last n).val = n` (see `Fin.val_last`).
-/
DefinitionDoc Fin.last as "Fin.last"

/-- `Fin.val_last n` states that `(Fin.last n).val = n`.

## Syntax
```
rw [Fin.val_last]    -- rewrites (Fin.last n).val to n
exact Fin.val_last n -- closes a goal (Fin.last n).val = n
```

## When to use it
When you need to compute or simplify the value of `Fin.last`.

## Example
```
-- Goal: (Fin.last 4).val = 4
exact Fin.val_last 4
```
-/
TheoremDoc Fin.val_last as "Fin.val_last" in "Fin"

NewDefinition Fin.last
NewTheorem Fin.val_last

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos
