import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 1

Title "Matrices Are Functions"

Introduction "
# What is a Matrix?

In Lean, a matrix is nothing more than a **function of two indices**:

$$M : \\text{Fin}\\ m \\to \\text{Fin}\\ n \\to \\alpha$$

The type `Matrix (Fin m) (Fin n) α` is literally defined as
`Fin m → Fin n → α`. A 2×3 matrix of integers is a function
`Fin 2 → Fin 3 → ℤ`.

To build a matrix from a function, use `Matrix.of`:

```
Matrix.of f    -- wraps a function f : m → n → α as a matrix
```

To read an entry, use `Matrix.of_apply`:

```
Matrix.of_apply : Matrix.of f i j = f i j
```

This says: accessing entry `(i, j)` of the matrix built from `f` is the
same as applying `f` to `i` and `j`. Matrices are functions — nothing
is hidden.

**Your task**: Build a matrix from a function and read off one of its entries.
"

/-- Accessing an entry of a matrix built from a function. -/
Statement : ∀ (f : Fin 2 → Fin 2 → ℤ), Matrix.of f 0 1 = f 0 1 := by
  Hint "Introduce the function `f`."
  intro f
  Hint "The goal asks you to show that accessing entry `(0, 1)` of
  `Matrix.of f` gives the same result as `f 0 1`. Rewrite with
  `Matrix.of_apply`."
  Hint (hidden := true) "Try `rw [Matrix.of_apply]`."
  rw [of_apply]

Conclusion "
`Matrix.of` wraps a function as a matrix, and `Matrix.of_apply` unwraps
it: accessing the matrix at `(i, j)` is the same as calling the function
at `(i, j)`.

**The takeaway**: In Lean, a matrix IS a function. All matrix reasoning
reduces to function reasoning. If you know how to work with functions
(and you do, from the Fin Tuples world), you know how to work with
matrices.

The entry access `M i j` works for any matrix `M` — the first index
selects the row, the second selects the column. This is just double
function application: `M` applied to `i` gives a row (a function
`Fin n → α`), which applied to `j` gives the entry.
"

/-- `Matrix.of_apply` evaluates a matrix built from a function:

`Matrix.of f i j = f i j`

## Syntax
```
rw [Matrix.of_apply]       -- in the goal
rw [Matrix.of_apply] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis contains `Matrix.of f i j` and you want
to simplify it to `f i j`.

## Example
`rw [Matrix.of_apply]` turns `Matrix.of (fun i j => i + j) 1 2 = 3`
into `1 + 2 = 3`.
-/
TheoremDoc Matrix.of_apply as "Matrix.of_apply" in "Matrix"

/-- `Matrix m n α` is the type of matrices with entries in `α`, rows
indexed by `m`, and columns indexed by `n`.

Internally, `Matrix m n α` is just `m → n → α` — a function of two
indices. For finite matrices, use `Matrix (Fin m) (Fin n) α`.

## Key operations
- `Matrix.of f` — build a matrix from a function
- `M i j` — access entry at row `i`, column `j`
- `Mᵀ` — transpose (swap rows and columns)
- `Matrix.diagonal d` — square matrix with `d` on the diagonal

## Key lemma
`Matrix.ext_iff : (∀ i j, M i j = N i j) ↔ M = N`
-/
DefinitionDoc Matrix as "Matrix"

/-- `Matrix.of` wraps a function `f : m → n → α` as a `Matrix m n α`.

Since `Matrix m n α` is defined as `m → n → α`, `Matrix.of` is just
a type cast — it changes the type without changing the data.

## Syntax
```
Matrix.of (fun i j => ...)
```

## When to use it
When you want to explicitly construct a matrix from a function.

## Key lemma
`Matrix.of_apply : Matrix.of f i j = f i j`
-/
DefinitionDoc Matrix.of as "Matrix.of"

TheoremTab "Matrix"
NewTheorem Matrix.of_apply
NewDefinition Matrix Matrix.of

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
