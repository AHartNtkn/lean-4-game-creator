import Game.Metadata

World "FinTuples"
Level 10

Title "Dropping the Last Element"

Introduction "
# Fin.init: The Dual of Fin.tail

You've seen `Fin.tail`, which drops the **first** element. Now meet
its dual:

**`Fin.init`** drops the **last** element.

Given a tuple `f : Fin (n + 1) → α`, `Fin.init f` is a shorter
tuple `Fin n → α` that keeps all elements except the last:

$$\\texttt{Fin.init}\\;f\\;(i) = f\\;(i.\\texttt{castSucc})$$

The definition uses `castSucc` — exactly the FinNavigation operation
that embeds `Fin n` into `Fin (n + 1)` without reaching the last index.

The duality:
- `Fin.tail` drops the first: `Fin.tail ![a, b, c] = ![b, c]`
- `Fin.init` drops the last: `Fin.init ![a, b, c]` has values `a, b`

**Your task**: Verify the values of `Fin.init ![a, b, c]`.
"

/-- `Fin.init` keeps all elements except the last. -/
Statement (a b c : ℕ) :
    (Fin.init (![a, b, c] : Fin 3 → ℕ)) 0 = a ∧
    (Fin.init (![a, b, c] : Fin 3 → ℕ)) 1 = b := by
  Hint "Use `constructor` to split the conjunction."
  constructor
  · Hint "`Fin.init ![a, b, c]` at index 0 is `![a, b, c]` at
    `0.castSucc = 0`, which is `a`. Use `rfl`."
    rfl
  · Hint "`Fin.init ![a, b, c]` at index 1 is `![a, b, c]` at
    `1.castSucc = 1`, which is `b`. Use `rfl`."
    rfl

Conclusion "
`Fin.init` and `Fin.tail` are complementary:

| Operation | Drops | Keeps | Routes through |
|---|---|---|---|
| `Fin.tail f` | First (`f 0`) | `f 1, f 2, ..., f n` | `succ` |
| `Fin.init f` | Last (`f (last n)`) | `f 0, f 1, ..., f (n-1)` | `castSucc` |

Notice how the FinNavigation decompositions appear again:
- `Fin.tail` uses **succ** (the `0`/`succ` decomposition)
- `Fin.init` uses **castSucc** (the `castSucc`/`last` decomposition)

In the next level, you'll see the reconstruction identity for
`Fin.init` and `vecSnoc` — the dual of `Fin.cons_self_tail`.
"

/-- `Fin.init f` drops the last element of tuple `f`.

## Syntax
```
Fin.init f    -- drop the last element
```

## Type
`Fin.init : (Fin (n + 1) → α) → (Fin n → α)`

## Definition
`Fin.init f i = f i.castSucc`

## Example
`Fin.init ![10, 20, 30]` has values `10` at index 0 and `20` at index 1.

## Key identity (taught in the next level)
`vecSnoc (Fin.init f) (f (Fin.last n)) = f` — every tuple equals
its init snoc'd with its last element (`vecSnoc_self_init`).
-/
DefinitionDoc Fin.init as "Fin.init"

NewDefinition Fin.init

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
