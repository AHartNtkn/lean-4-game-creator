import Game.Metadata

World "FinTuples"
Level 4

Title "Prepending with Fin.cons"

Introduction "
# Fin.cons: Building Tuples One Element at a Time

Under the hood, `![a, b, c]` is built using **`Fin.cons`** —
a function that prepends one element to an existing tuple.

`Fin.cons` takes:
- An element `a : α` (the new head)
- A tuple `f : Fin n → α` (the existing tail)

and produces a tuple `Fin.cons a f : Fin (n + 1) → α` that
starts with `a` followed by the elements of `f`.

The notation `![a, b, c]` is shorthand for nested `Fin.cons`:
$$\\texttt{![a, b, c]} = \\texttt{Fin.cons } a \\;\\texttt{![b, c]}$$

This is the tuple analog of how `List.cons` builds lists —
prepend one element at a time.

**Your task**: Prove that `![a, b, c]` equals `Fin.cons a ![b, c]`.
This is true by definition.
"

/-- `![a, b, c]` is the same as `Fin.cons a ![b, c]`. -/
Statement (a b c : ℕ) :
    (![a, b, c] : Fin 3 → ℕ) = Fin.cons a ![b, c] := by
  Hint "This equality holds by definition — `![a, b, c]`
  IS `Fin.cons a ![b, c]`. Use `rfl`."
  rfl

Conclusion "
`Fin.cons` is the fundamental building block for tuples:
- Start with the empty tuple `![] : Fin 0 → α`
- Prepend `c`: `Fin.cons c ![] = ![c] : Fin 1 → α`
- Prepend `b`: `Fin.cons b ![c] = ![b, c] : Fin 2 → α`
- Prepend `a`: `Fin.cons a ![b, c] = ![a, b, c] : Fin 3 → α`

Each `Fin.cons` increases the tuple length by 1.

This is the `Fin` analog of how $\\texttt{cons}$ builds linked lists.
The difference: a linked list has variable length, while
`Fin n → α` has the length `n` baked into the type.
"

/-- `Fin.cons a f` prepends element `a` to tuple `f`,
producing a tuple of length `n + 1`.

## Syntax
```
Fin.cons a f      -- explicit
![a, b, c]        -- ![a, b, c] = Fin.cons a ![b, c]
```

## Type
`Fin.cons : α → (Fin n → α) → (Fin (n + 1) → α)`

## Element access
- `Fin.cons a f 0 = a` (the new head) — `Fin.cons_val_zero`
- `Fin.cons a f i.succ = f i` (the old tail) — `Fin.cons_val_succ`

## Example
`Fin.cons 10 ![20, 30] = ![10, 20, 30]`
-/
DefinitionDoc Fin.cons as "Fin.cons"

NewDefinition Fin.cons

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
