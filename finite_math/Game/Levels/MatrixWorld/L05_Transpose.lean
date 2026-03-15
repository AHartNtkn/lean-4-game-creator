import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 5

Title "Matrix transpose"

Introduction
"
# `Matrix.transpose`: Transposing a Matrix

The **transpose** of a matrix swaps rows and columns: entry `(i, j)`
of `M` becomes entry `(j, i)` of `Mᵀ`. In Lean:

```
Matrix.transpose (M : Matrix m n α) : Matrix n m α
```

Note the type change: an `m × n` matrix becomes an `n × m` matrix.

## The evaluation rule

```
Matrix.transpose_apply : M.transpose i j = M j i
```

This is the entire definition: transposing swaps the two function
arguments.

## Notation

You can write `M.transpose` using dot notation. (The superscript `ᵀ`
notation requires a scope that we will not open here.)

## Your task

Prove that transposing `!![1, 2; 3, 4]` swaps the off-diagonal entries.
"

/-- Transposing swaps the off-diagonal entries. -/
Statement : (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int).transpose 0 1 = 3 ∧
    (!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Int).transpose 1 0 = 2 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "Use `rw [Matrix.transpose_apply]` to swap the indices.
    The goal becomes `!![1, 2; 3, 4] 1 0 = 3`, which reduces by `rfl`."
    Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`."
    rw [Matrix.transpose_apply]
    rfl
  · Hint "Same approach: `rw [Matrix.transpose_apply]` swaps the indices."
    Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`."
    rw [Matrix.transpose_apply]
    rfl

Conclusion
"
You verified that transposing swaps off-diagonal entries.

## What transpose does

For a matrix $A$ with entries $a_{ij}$:

$$A^T_{ij} = a_{ji}$$

In Lean: `M.transpose i j = M j i`. That is the entire story — transpose
just swaps the two function arguments.

## Diagonal matrices are symmetric

A diagonal matrix satisfies $D^T = D$ because its off-diagonal entries
are all zero. The lemma `Matrix.diagonal_transpose` captures this:

```
Matrix.diagonal_transpose : (Matrix.diagonal d).transpose = Matrix.diagonal d
```

## In ordinary mathematics

On paper:
$$\\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}^T =
\\begin{pmatrix} 1 & 3 \\\\ 2 & 4 \\end{pmatrix}$$

In Lean, this is just swapping the argument order of a two-argument function.

**In plain language**: \"Transposing a matrix = swapping the row and column
arguments of the underlying function.\"
"

/-- `Matrix.transpose M` swaps the rows and columns of `M`:

`M.transpose i j = M j i`

**Type**: `Matrix m n α → Matrix n m α`

**Key lemma**: `Matrix.transpose_apply : M.transpose i j = M j i`

**Fact**: Diagonal matrices are symmetric: `(Matrix.diagonal d).transpose = Matrix.diagonal d`. -/
DefinitionDoc Matrix.transpose as "Matrix.transpose"

/-- `Matrix.transpose_apply` evaluates a transposed matrix entry:

`M.transpose i j = M j i`

**When to use**: Whenever you need to simplify an entry of a transposed
matrix. The result swaps the two indices. -/
TheoremDoc Matrix.transpose_apply as "Matrix.transpose_apply" in "Matrix"

NewDefinition Matrix.transpose
NewTheorem Matrix.transpose_apply
TheoremTab "Matrix"
DisabledTactic trivial decide native_decide simp aesop simp_all
