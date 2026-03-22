import Game.Metadata

World "FinNavigation"
Level 4

Title "Moving Forward: Fin.succ"

Introduction "
# Fin.succ: The Next Element

There's a second way to go from `Fin n` to `Fin (n+1)`:
**`Fin.succ`**, which **increments** the value by 1.

If `i : Fin n` has value `k`, then `i.succ : Fin (n+1)` has
value `k + 1`.

Compare with `castSucc`:
- `i.castSucc.val = i.val` (same value)
- `i.succ.val = i.val + 1` (value plus one)

Both send `Fin n → Fin (n+1)`, but they land at different
positions. `castSucc` keeps you in place; `succ` moves you
forward by one.

The theorem **`Fin.val_succ`** states:
$$\\texttt{i.succ.val} = \\texttt{i.val} + 1$$

**Your task**: Prove this value relationship.
"

/-- `Fin.succ` increments the underlying value by 1. -/
Statement : ∀ i : Fin 3, (i.succ).val = i.val + 1 := by
  Hint "Start with `intro i`, then use `exact Fin.val_succ i`."
  intro i
  exact Fin.val_succ i

Conclusion "
(As with `Fin.val_last` and `Fin.val_castSucc`, `rfl` also works
here since the definition is transparent. But `Fin.val_succ` is
the rewrite tool you'll need when `n` is a variable.)

You now have the three navigation functions and their val lemmas:

| Function | Type | Value |
|---|---|---|
| `Fin.last n` | `Fin (n+1)` | `n` |
| `i.castSucc` | `Fin n → Fin (n+1)` | `i.val` (unchanged) |
| `i.succ` | `Fin n → Fin (n+1)` | `i.val + 1` |

The val lemmas (`val_last`, `val_castSucc`, `val_succ`) convert
`Fin` navigation into plain arithmetic. The strategy for proving
`Fin` facts is: **rewrite to values, then omega**.

In the next level, you'll combine these val lemmas to prove a
relationship between `castSucc` and `succ`.
"

/-- `Fin.succ` maps `Fin n` to `Fin (n + 1)` by adding 1 to the
underlying value.

## Syntax
```
i.succ      -- dot notation
Fin.succ i  -- explicit
```

## Type
`Fin.succ : Fin n → Fin (n + 1)`

## Value
`i.succ.val = i.val + 1` (see `Fin.val_succ`)

## Comparison with castSucc
- `castSucc`: same value, bigger type
- `succ`: value + 1, bigger type
-/
DefinitionDoc Fin.succ as "Fin.succ"

/-- `Fin.val_succ i` states that `i.succ.val = i.val + 1`.

## Syntax
```
rw [Fin.val_succ]      -- rewrites i.succ.val to i.val + 1
exact Fin.val_succ i   -- closes the goal directly
```

## When to use it
When you need to simplify `Fin.succ` to the underlying value.
-/
TheoremDoc Fin.val_succ as "Fin.val_succ" in "Fin"

NewDefinition Fin.succ
NewTheorem Fin.val_succ

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos
