import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 7

Title "Computing a matrix product"

Introduction
"
# Computing a Concrete Matrix Product

Now you will put `mul_apply` and `sum_univ_two` to work on a
concrete computation. Given:

$$A = \\begin{pmatrix} 1 & 2 \\\\ 3 & 4 \\end{pmatrix}, \\quad
  B = \\begin{pmatrix} 5 & 6 \\\\ 7 & 8 \\end{pmatrix}$$

You will prove that $(A \\cdot B)_{00} = 19$.

## The hand computation

$$(AB)_{00} = a_{00} b_{00} + a_{01} b_{10} = 1 \\cdot 5 + 2 \\cdot 7 = 5 + 14 = 19$$

## The Lean proof

1. `rw [Matrix.mul_apply]` — expand the product entry into a sum
2. `rw [Fin.sum_univ_two]` — unfold the sum into two terms
3. `norm_num` — evaluate the arithmetic

This is the same pattern from Level 6, now with concrete numbers.
"

/-- The `(0, 0)` entry of a concrete matrix product. -/
Statement : (!![1, 2; 3, 4] * !![5, 6; 7, 8] : Matrix (Fin 2) (Fin 2) Int) 0 0 = 19 := by
  Hint "First, expand the product entry: `rw [Matrix.mul_apply]`.

  Then unfold the sum: `rw [Fin.sum_univ_two]`.

  Finally, evaluate the arithmetic: `norm_num`."
  Hint (hidden := true) "Try `rw [Matrix.mul_apply, Fin.sum_univ_two]` then `norm_num`."
  rw [Matrix.mul_apply]
  Hint "The goal is now `∑ j, !![1, 2; 3, 4] 0 j * !![5, 6; 7, 8] j 0 = 19`.

  Unfold the sum with `rw [Fin.sum_univ_two]`."
  rw [Fin.sum_univ_two]
  Hint "The goal is now `1 * 5 + 2 * 7 = 19` (or something equivalent after
  evaluation of the matrix entries). Use `norm_num` to finish the arithmetic."
  Hint (hidden := true) "Try `norm_num`."
  norm_num

Conclusion
"
You computed a concrete matrix product entry!

## The three-step pattern

For any concrete matrix product entry:

1. **`rw [Matrix.mul_apply]`** — expand into a sum
2. **`rw [Fin.sum_univ_two]`** — unfold the sum (for $2 \\times 2$)
3. **`norm_num`** — evaluate the arithmetic

This pattern scales: for $3 \\times 3$ matrices, use `Fin.sum_univ_three`
instead, and `norm_num` handles the longer arithmetic.

## Verifying by hand

$$(AB)_{00} = 1 \\cdot 5 + 2 \\cdot 7 = 5 + 14 = 19 \\checkmark$$

Each step in the Lean proof corresponds to a step in the hand computation:
expanding the dot product, listing the terms, and doing the arithmetic.

**In plain language**: \"To compute a matrix product entry, take the
dot product of the corresponding row and column. In Lean, `mul_apply`
writes this as a sum, and `sum_univ_two` expands the sum into explicit
terms.\"
"

DisabledTactic trivial decide native_decide simp aesop simp_all
