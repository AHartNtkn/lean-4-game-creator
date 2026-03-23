import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 8

Title "Diagonal Matrix: On-Diagonal Entry"

Introduction "
# Diagonal Matrices

A **diagonal matrix** has nonzero entries only on the main diagonal
(where the row index equals the column index). All off-diagonal entries
are zero.

In Lean, `Matrix.diagonal d` builds a square matrix from a function
`d : n → α`:

$$\\text{diagonal}\\,d\\,i\\,j = \\begin{cases} d\\,i & \\text{if } i = j \\\\\\\\ 0 & \\text{if } i \\neq j \\end{cases}$$

The key lemma for **on-diagonal** entries is `Matrix.diagonal_apply_eq`:

```
Matrix.diagonal_apply_eq : (diagonal d) i i = d i
```

When the row and column indices are the same (`i = i`), the diagonal
matrix returns `d i`.

**Your task**: Read an on-diagonal entry of a diagonal matrix.
"

/-- Read an on-diagonal entry of a diagonal matrix. -/
Statement (d : Fin 3 → ℤ) : (diagonal d) 1 1 = d 1 := by
  Hint "The goal asks for the value of `diagonal d` at position `(1, 1)`.
  Since the row and column match, this is an on-diagonal entry.
  Use `Matrix.diagonal_apply_eq`."
  Hint (hidden := true) "Try `rw [Matrix.diagonal_apply_eq]`."
  rw [diagonal_apply_eq]

Conclusion "
When both indices are the same, `diagonal d` just returns the diagonal
value `d i`. The lemma `Matrix.diagonal_apply_eq` captures this:

$$\\text{diagonal}\\,d\\,i\\,i = d\\,i$$

This is one half of the diagonal definition. The other half — what
happens when the indices differ — comes in the next level.

**Pattern**: `rw [Matrix.diagonal_apply_eq]` when you see
`(diagonal d) i i` (same index twice).

**Connection**: The most famous diagonal matrix is the **identity
matrix**, which is `diagonal (fun _ => 1)`. By `diagonal_apply_eq`,
each on-diagonal entry `(diagonal (fun _ => 1)) i i = 1`, and by
`diagonal_apply_ne` (next level), each off-diagonal entry is `0`.
In Lean, `(1 : Matrix (Fin n) (Fin n) α)` is exactly this `diagonal`
applied to the constant function `1`.
"

/-- `Matrix.diagonal_apply_eq` evaluates a diagonal matrix on the diagonal:

`(diagonal d) i i = d i`

When the row and column indices are equal, the diagonal matrix
returns the diagonal value.

## Syntax
```
rw [Matrix.diagonal_apply_eq]
```

## When to use it
When the goal contains `(diagonal d) i i` where both indices are
the same variable or the same concrete value.

## Example
`rw [Matrix.diagonal_apply_eq]` turns `(diagonal d) 2 2 = d 2`
into `d 2 = d 2`.
-/
TheoremDoc Matrix.diagonal_apply_eq as "Matrix.diagonal_apply_eq" in "Matrix"

/-- `Matrix.diagonal d` builds a square matrix with `d` on the diagonal
and `0` everywhere else.

## Syntax
```
Matrix.diagonal d    -- where d : n → α
```

## Key lemmas
- `Matrix.diagonal_apply_eq : (diagonal d) i i = d i`
- `Matrix.diagonal_apply_ne : i ≠ j → (diagonal d) i j = 0`

## Example
`diagonal (fun i : Fin 3 => i.val + 1)` is the matrix
with entries 1, 2, 3 on the diagonal and 0 elsewhere.
-/
DefinitionDoc Matrix.diagonal as "Matrix.diagonal"

TheoremTab "Matrix"
NewTheorem Matrix.diagonal_apply_eq
NewDefinition Matrix.diagonal

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_apply
