import GameServer.Commands
import Mathlib

World "Capstone"
Level 6

Title "Matrix trace as a sum"

Introduction
"
# Matrix trace: big operators meet matrices

The **trace** of a square matrix is the sum of its diagonal entries:

$$\\text{tr}(M) = \\sum_{i} M_{ii}$$

In Mathlib, `Matrix.trace M = ∑ i, M i i`. This directly uses the
big-operator machinery you learned in the **FinsetSum** / **BigOpAdvanced**
worlds, applied to the matrix representation from **MatrixWorld**.

## Your task

Compute the trace of the diagonal matrix with entries `1, 2, 3`
(indexed by `Fin 3`):

$$\\text{tr}\\left(\\text{diag}(1, 2, 3)\\right) = 1 + 2 + 3 = 6$$

## Strategy

1. `Matrix.trace_diagonal` — reduces `trace(diag(d))` to `∑ i, d i`.
2. `Fin.sum_univ_three` — expands the sum over `Fin 3` into three terms.
3. `norm_num` — evaluates the arithmetic.
"

/-- The trace of `diag(1, 2, 3)` is 6. -/
Statement : (Matrix.diagonal (fun i : Fin 3 => (i : ℤ) + 1)).trace = 6 := by
  Hint "**Step 1**: Use `rw [Matrix.trace_diagonal]` to reduce the trace
  of a diagonal matrix to a sum: `∑ i, d i`."
  Hint (hidden := true) "Try `rw [Matrix.trace_diagonal]`."
  rw [Matrix.trace_diagonal]
  Hint "**Step 2**: The goal is `∑ i : Fin 3, ((i : ℤ) + 1) = 6`.

  Expand the sum with `rw [Fin.sum_univ_three]` to get
  `((0 : ℤ) + 1) + ((1 : ℤ) + 1) + ((2 : ℤ) + 1) = 6`."
  Hint (hidden := true) "Try `rw [Fin.sum_univ_three]`."
  rw [Fin.sum_univ_three]
  Hint "Close with `norm_num`."
  Hint (hidden := true) "Try `norm_num`."
  norm_num

Conclusion
"
You computed a matrix trace by reducing it to a finite sum:

1. **`trace_diagonal`** — trace of a diagonal matrix = sum of diagonal entries.
2. **`sum_univ_three`** — expand the sum over `Fin 3` into explicit terms.
3. **`norm_num`** — evaluate `1 + 2 + 3 = 6`.

## The cross-module connection

This proof uses three modules:
- **Matrix** (`Matrix.diagonal`, `Matrix.trace_diagonal`)
- **Big operators** (`Fin.sum_univ_three`)
- **Fin** (the index type `Fin 3`, coercion `(i : ℤ)`)

The trace is fundamentally a big-operator concept applied to a matrix.
In Lean, this is not a metaphor — the trace is *defined* as `∑ i, M i i`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
