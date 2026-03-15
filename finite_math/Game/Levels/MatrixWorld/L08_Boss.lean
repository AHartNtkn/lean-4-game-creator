import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 8

Title "Boss: squaring an upper-triangular matrix"

Introduction
"
# Boss: Squaring an Upper-Triangular Matrix

Time to integrate everything from this world. You will prove two facts
about the upper-triangular matrix:

$$A = \\begin{pmatrix} 1 & 2 \\\\ 0 & 1 \\end{pmatrix}$$

**Part 1**: $A^2 = \\begin{pmatrix} 1 & 4 \\\\ 0 & 1 \\end{pmatrix}$

**Part 2**: $(A^2)^T_{01} = 0$

## Strategy for Part 1

To prove matrix equality, use `ext i j` to reduce to entry-wise
equality. Then for each entry:

1. `rw [Matrix.mul_apply]` — expand the product
2. `rw [Fin.sum_univ_two]` — unfold the sum
3. `norm_num` — evaluate the arithmetic

Since `A * A` has four entries and `Fin 2` has two elements for each
index, `fin_cases i <;> fin_cases j` generates all four cases at once.

## Strategy for Part 2

After Part 1, you know `A * A = !![1, 4; 0, 1]`. Part 2 asks for
`(A * A).transpose 0 1 = 0`. Use:

1. `rw [Matrix.transpose_apply]` — swap the indices
2. `rw [Matrix.mul_apply, Fin.sum_univ_two]` — expand the product
3. `norm_num` — evaluate

## Your task

Prove both parts as a conjunction.
"

/-- Squaring the upper-triangular matrix gives `!![1, 4; 0, 1]`,
and the `(0, 1)` entry of its transpose is `0`. -/
Statement : (!![1, 2; 0, 1] * !![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) Int) = !![1, 4; 0, 1] ∧
    (!![1, 2; 0, 1] * !![1, 2; 0, 1] : Matrix (Fin 2) (Fin 2) Int).transpose 0 1 = 0 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "**Part 1**: Prove the matrix equality.

    Use `ext i j` to reduce to entry-wise equality, then
    `fin_cases i <;> fin_cases j` to split into four cases.

    In each case, use `rw [Matrix.mul_apply, Fin.sum_univ_two]` and
    `norm_num` to compute the entry."
    Hint (hidden := true) "Try:
    ```
    ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> norm_num
    ```"
    ext i j
    Hint "Now use `rw [Matrix.mul_apply, Fin.sum_univ_two]` to expand
    the product entry, then `fin_cases i <;> fin_cases j <;> norm_num`."
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    fin_cases i <;> fin_cases j <;> norm_num
  · Hint "**Part 2**: Prove that `(A * A).transpose 0 1 = 0`.

    Use `rw [Matrix.transpose_apply]` to swap the indices (goal becomes
    `(A * A) 1 0 = 0`), then expand the product entry and compute."
    Hint (hidden := true) "Try:
    ```
    rw [Matrix.transpose_apply]
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num
    ```"
    rw [Matrix.transpose_apply]
    Hint "The goal is now `(!![1, 2; 0, 1] * !![1, 2; 0, 1]) 1 0 = 0`.

    Expand the product: `rw [Matrix.mul_apply, Fin.sum_univ_two]`, then
    `norm_num`."
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    norm_num

Conclusion
"
Congratulations on completing the **Matrices as Functions** world!

You proved that squaring an upper-triangular matrix preserves the
upper-triangular structure (the `(1, 0)` entry stays zero), and you
verified this through both direct computation and the transpose.

## What you learned in this world

| Level | Key lesson | Key item |
|-------|-----------|----------|
| L01 | `Matrix m n α = m → n → α` | `Matrix` definition |
| L02 | Constructing a matrix = defining a function | Function construction |
| L03 | `ext i j` + `fin_cases` for matrix equality | `ext` for matrices |
| L04 | `Matrix.diagonal` and `diagonal_apply` | `Matrix.diagonal` |
| L05 | `Matrix.transpose` and `transpose_apply` | `Matrix.transpose` |
| L06 | `Matrix.mul_apply` + `Fin.sum_univ_two` | `Matrix.mul_apply` |
| L07 | Computing a concrete product entry | Three-step pattern |
| L08 | Boss: integrating all skills | Full chain |

## The proof pattern

For concrete matrix computations in Lean:

1. **Equality**: `ext i j` + `fin_cases i <;> fin_cases j`
2. **Product entries**: `rw [Matrix.mul_apply, Fin.sum_univ_two]`
3. **Transpose entries**: `rw [Matrix.transpose_apply]`
4. **Diagonal entries**: `rw [Matrix.diagonal_apply]`
5. **Arithmetic**: `norm_num`

## Transfer moment

In ordinary mathematics, you verify $A^2$ by computing each entry:

$$A^2_{00} = 1 \\cdot 1 + 2 \\cdot 0 = 1, \\quad
  A^2_{01} = 1 \\cdot 2 + 2 \\cdot 1 = 4$$
$$A^2_{10} = 0 \\cdot 1 + 1 \\cdot 0 = 0, \\quad
  A^2_{11} = 0 \\cdot 2 + 1 \\cdot 1 = 1$$

In Lean, `mul_apply` writes the dot product, `sum_univ_two` expands it,
and `norm_num` does the arithmetic. The proof structure exactly mirrors
the hand computation.

## The big picture

Matrices in Lean are functions over finite types. Matrix multiplication
uses `∑` — the same finite sums you mastered earlier. Transpose swaps
function arguments. Diagonal matrices are conditional functions. The
entire matrix API reduces to operations you already know.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
