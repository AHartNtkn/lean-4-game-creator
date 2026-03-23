import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 3

Title "Transpose: Flipping Rows and Columns"

Introduction "
# Transposing a Matrix

The **transpose** of a matrix swaps rows and columns. If `M` is an
$m \\times n$ matrix, then $M^T$ is an $n \\times m$ matrix where
entry $(i, j)$ of $M^T$ is entry $(j, i)$ of $M$.

In Lean, the transpose is written `Mᵀ` (using the notation `ᵀ`
from the `Matrix` scope). The key lemma is:

```
Matrix.transpose_apply : Mᵀ i j = M j i
```

Since a matrix is a function, transposing just swaps the arguments:
`Mᵀ i j = M j i`.

**Your task**: Given that `M 2 0 = 7`, read the entry `Mᵀ 0 2`.
"

/-- Read a transpose entry using `transpose_apply`. -/
Statement (M : Matrix (Fin 3) (Fin 3) ℤ) (h : M 2 0 = 7) : Mᵀ 0 2 = 7 := by
  Hint "The goal involves `Mᵀ 0 2`. Transpose swaps the indices, so
  `Mᵀ 0 2 = M 2 0`. Rewrite with `Matrix.transpose_apply` to make
  this substitution."
  Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`. The goal
  becomes `M 2 0 = 7`."
  rw [transpose_apply]
  Hint "Now the goal is `M 2 0 = 7`, which is exactly your hypothesis
  `{h}`."
  Hint (hidden := true) "Try `exact h`."
  exact h

Conclusion "
`Matrix.transpose_apply` is the workhorse for transpose reasoning.
It says `Mᵀ i j = M j i` — reading row `i`, column `j` of the
transpose is the same as reading row `j`, column `i` of the original.

Since `Matrix` is just a function type, `transpose M i j = M j i` —
the transpose literally swaps the two function arguments. The `ᵀ`
notation is cosmetic sugar for this argument swap.

**Pattern**: When you see `Mᵀ i j` in a goal, rewrite with
`Matrix.transpose_apply` to get `M j i`.
"

/-- `Matrix.transpose_apply` evaluates a transpose entry:

`Mᵀ i j = M j i`

The transpose swaps rows and columns: entry `(i, j)` of the
transpose is entry `(j, i)` of the original.

## Syntax
```
rw [Matrix.transpose_apply]       -- in the goal
rw [Matrix.transpose_apply] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis contains `Mᵀ i j`.

## Example
`rw [Matrix.transpose_apply]` turns `Mᵀ 0 2 = 7` into `M 2 0 = 7`.
-/
TheoremDoc Matrix.transpose_apply as "Matrix.transpose_apply" in "Matrix"

/-- `Matrix.transpose M` (notation: `Mᵀ`) swaps the rows and columns
of a matrix. If `M` is an `m × n` matrix, then `Mᵀ` is an `n × m`
matrix.

## Syntax
```
Mᵀ      -- transpose notation
```

## Key lemma
`Matrix.transpose_apply : Mᵀ i j = M j i`
-/
DefinitionDoc Matrix.transpose as "Matrix.transpose"

TheoremTab "Matrix"
NewTheorem Matrix.transpose_apply
NewDefinition Matrix.transpose

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
