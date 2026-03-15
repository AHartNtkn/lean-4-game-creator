import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 2

Title "Constructing a 2x2 matrix"

Introduction
"
# Constructing a Matrix

Since `Matrix m n α` is just `m → n → α`, you construct a matrix by
writing a function. Here is a $2 \\times 2$ matrix defined as a function:

```
fun i j : Fin 2 => (i.val + 1) * (j.val + 1)
```

This function maps each pair of row and column indices to a value.
Since `Fin 2` has elements `0` and `1`, the entries are:

| | col 0 | col 1 |
|---|---|---|
| **row 0** | $(0+1)(0+1) = 1$ | $(0+1)(1+1) = 2$ |
| **row 1** | $(1+1)(0+1) = 2$ | $(1+1)(1+1) = 4$ |

## Matrix notation

Mathlib also provides the notation `!![a, b; c, d]` for concrete
matrices (the `!!` signals matrix literal). Under the hood, this
builds the same function. You will see this notation in later levels.

## Your task

Prove that the entry at row 1, column 1 of the function-defined
matrix equals 4. Since the matrix IS the function, this is just
function evaluation — `rfl` suffices.
"

/-- Entry `(1, 1)` of the function-defined matrix is `4`. -/
Statement : (fun i j : Fin 2 => (i.val + 1) * (j.val + 1) : Matrix (Fin 2) (Fin 2) Nat) 1 1 = 4 := by
  Hint "Since the matrix is defined as `fun i j => (i.val + 1) * (j.val + 1)`,
  evaluating at `i = 1, j = 1` gives `(1 + 1) * (1 + 1) = 4`.

  This is definitional: use `rfl`."
  Hint (hidden := true) "Try `rfl`."
  rfl

Conclusion
"
You constructed a matrix as a function and accessed an entry by
applying the function to concrete indices.

## The key insight

Because `Matrix m n α = m → n → α`, matrix construction is just
function definition, and entry access is just function application.
There is no special \"matrix indexing\" operation — Lean's ordinary
function application `M i j` does the job.

## The `!![...]` notation

For concrete matrices with small dimensions, Mathlib provides:

```
!![1, 2; 3, 4] : Matrix (Fin 2) (Fin 2) Nat
```

The semicolons separate rows. This is equivalent to writing:

```
fun i j : Fin 2 => ...
```

with the right case analysis built in. You will use this notation
starting in the next level.

**In plain language**: \"A matrix is a function. To build one, define
the function. To read an entry, apply the function.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
