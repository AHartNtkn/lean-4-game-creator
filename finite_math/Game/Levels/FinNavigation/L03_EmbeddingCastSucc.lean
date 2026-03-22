import Game.Metadata

World "FinNavigation"
Level 3

Title "Embedding with castSucc"

Introduction "
# Fin.castSucc: Same Value, Bigger Type

What if you have an element of `Fin n` and need it in `Fin (n+1)`?

**`Fin.castSucc`** does exactly this: it takes `i : Fin n` and
returns `i.castSucc : Fin (n+1)` with the **same value**.

For example, if `i : Fin 3` has value `2`, then
`i.castSucc : Fin 4` also has value `2`. The number doesn't
change — only the type's upper bound increases.

The theorem **`Fin.val_castSucc`** makes this precise:
$$\\texttt{i.castSucc.val} = \\texttt{i.val}$$

Why does this work? If `i.val < n`, then certainly `i.val < n+1`.
So the same number satisfies the stricter bound.

**Your task**: Prove that `castSucc` preserves the value.
"

/-- `castSucc` preserves the underlying value. -/
Statement : ∀ i : Fin 3, (i.castSucc).val = i.val := by
  Hint "Start with `intro i`, then use `exact Fin.val_castSucc i`."
  intro i
  exact Fin.val_castSucc i

Conclusion "
`Fin.castSucc` is an **embedding**: it maps `Fin n` into
`Fin (n+1)` without changing any values. Think of it as
*widening the frame* — the elements stay in place, but the
type now has room for one more element at the top.

**Why not automatic coercion?** You might wonder why Lean doesn't
just automatically treat `Fin n` elements as `Fin (n+1)` elements.
The reason: Lean's type system doesn't have a built-in coercion
from `Fin n` to `Fin m` for arbitrary `n <= m`. Each embedding must
be explicit, and `castSucc` is the standard one for the `n -> n+1`
step. This explicitness prevents silent type-widening bugs.

(Since the definition is transparent, `rfl` also works here —
just as it did for `Fin.val_last` in Level 1. But
`Fin.val_castSucc` is the tool you'll need when `n` is a
variable, so practice using the named lemma.)

The element that occupies that new top position is `Fin.last n`
(from Level 1). So `Fin (n+1)` consists of:
- The images of `Fin.castSucc` (values $0, \\ldots, n-1$)
- `Fin.last n` (value $n$)

You'll prove this decomposition in the boss level.

In plain math: the inclusion $\\{0, \\ldots, n-1\\} \\hookrightarrow
\\{0, \\ldots, n\\}$ is the identity on elements.
"

/-- `Fin.castSucc` embeds `Fin n` into `Fin (n + 1)` by keeping
the same value but relaxing the upper bound.

## Syntax
```
i.castSucc      -- dot notation
Fin.castSucc i  -- explicit
```

## Type
`Fin.castSucc : Fin n → Fin (n + 1)`

## Value
`i.castSucc.val = i.val` (see `Fin.val_castSucc`)

## When to use it
When you need to treat an element of `Fin n` as an element of
`Fin (n + 1)` without changing its value.
-/
DefinitionDoc Fin.castSucc as "Fin.castSucc"

/-- `Fin.val_castSucc i` states that `i.castSucc.val = i.val`.

## Syntax
```
rw [Fin.val_castSucc]      -- rewrites i.castSucc.val to i.val
exact Fin.val_castSucc i   -- closes the goal directly
```

## When to use it
When you need to simplify `castSucc` to the underlying value.
-/
TheoremDoc Fin.val_castSucc as "Fin.val_castSucc" in "Fin"

NewDefinition Fin.castSucc
NewTheorem Fin.val_castSucc

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem Fin.castSucc_lt_succ Fin.succ_pos
