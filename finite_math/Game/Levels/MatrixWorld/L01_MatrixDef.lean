import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 1

Title "Matrix as a function"

Introduction
"
# Matrices as Functions over Finite Types

Welcome to the **Matrix** world!

## The big idea

In linear algebra, a matrix is a rectangular grid of numbers. In
Lean's Mathlib, a matrix is something even simpler: **a function of
two arguments**.

The type `Matrix m n α` is *defined* as `m → n → α` — a function
from row indices `m` and column indices `n` to entries of type `α`.

So a $2 \\times 2$ matrix of natural numbers has type
`Matrix (Fin 2) (Fin 2) Nat`, which is literally `Fin 2 → Fin 2 → Nat`.

## Why this definition?

This functional definition means:
- **Constructing** a matrix = defining a function
- **Accessing** an entry `M i j` = applying a function
- **Equality** of matrices = extensional equality of functions

The finite-type infrastructure you built earlier (`Fin`, `Finset`,
`Fintype`, big operators) now becomes the backbone of matrix theory.

## Your task

Prove that `Matrix (Fin 2) (Fin 2) Int` is *definitionally* equal to
`Fin 2 → Fin 2 → Int`. Since `Matrix m n α` is defined as
`m → n → α`, this is true by `rfl`.
"

/-- `Matrix (Fin 2) (Fin 2) Int` is definitionally equal to `Fin 2 → Fin 2 → Int`. -/
Statement : Matrix (Fin 2) (Fin 2) Int = (Fin 2 → Fin 2 → Int) := by
  Hint "Since `Matrix m n α` is *defined* as `m → n → α`, the two types
  are definitionally equal. Use `rfl` to close the goal."
  Hint (hidden := true) "Try `rfl`."
  rfl

Conclusion
"
You proved the foundational fact: `Matrix (Fin 2) (Fin 2) Int` is literally
the same type as `Fin 2 → Fin 2 → Int`.

## What this means

Every operation on matrices — construction, entry access, addition,
multiplication, transposition — is an operation on functions. Lean does
not need a separate \"matrix\" data structure because functions over
finite types already have all the required properties.

## In ordinary mathematics

On paper, you write a matrix as a grid:
$$A = \\begin{pmatrix} a_{00} & a_{01} \\\\ a_{10} & a_{11} \\end{pmatrix}$$

In Lean, $A$ is a function: `A i j` gives the entry in row `i`, column `j`.
The grid is just notation for the function's values on all input pairs.

## What comes next

In the next level, you will construct a concrete $2 \\times 2$ matrix
by writing a function.
"

/-- `Matrix m n α` is the type of matrices with rows indexed by `m`,
columns indexed by `n`, and entries of type `α`.

**Definition**: `Matrix m n α = m → n → α`

A matrix is a function of two arguments: a row index and a column index.

**Key consequence**: Constructing a matrix means defining a function.
Accessing entry `M i j` means applying the function. -/
DefinitionDoc Matrix as "Matrix"

NewDefinition Matrix
TheoremTab "Matrix"
DisabledTactic trivial decide native_decide simp aesop simp_all
