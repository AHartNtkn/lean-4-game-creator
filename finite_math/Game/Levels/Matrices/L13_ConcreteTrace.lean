import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 13

Title "Computing a Trace with Actual Numbers"

Introduction "
# Trace of a Concrete Matrix

In Level 12, you proved that the trace of `diagonal d` equals `∑ i, d i`
using `Finset.sum_congr rfl` and entry-level rewrites. That was a
symbolic result — you showed two sums are equal without computing a
number.

Now you will compute a trace with **actual numbers**.

Given a diagonal function `d` with known values `d 0 = 3`, `d 1 = 0`,
`d 2 = 7`, the trace of `diagonal d` should be `3 + 0 + 7 = 10`.

**New tool: `Fin.sum_univ_three`**

To evaluate a sum over `Fin 3` to a concrete expression, use:

```
Fin.sum_univ_three : ∑ i : Fin 3, f i = f 0 + f 1 + f 2
```

This converts the abstract `∑` into an explicit sum of three terms.
After that, you can use `diag_apply` and `diagonal_apply_eq` to
evaluate each term, and `ring` to close the arithmetic.

**Your task**: Compute the trace of a diagonal matrix with known values.
"

/-- The trace of a diagonal matrix with known values evaluates to a number. -/
Statement (d : Fin 3 → ℤ) (h0 : d 0 = 3) (h1 : d 1 = 0) (h2 : d 2 = 7) :
    ∑ i, diag (diagonal d) i = 10 := by
  Hint "First, expand the sum over `Fin 3` into three explicit terms
  using `Fin.sum_univ_three`."
  Hint (hidden := true) "Try `rw [Fin.sum_univ_three]`. The goal
  becomes `diag (diagonal d) 0 + diag (diagonal d) 1 + diag (diagonal d) 2 = 10`."
  rw [Fin.sum_univ_three]
  Hint "Now each term has the form `diag (diagonal d) i`. Use
  `diag_apply` to peel `diag`, then `diagonal_apply_eq` to evaluate
  the on-diagonal entries."
  Hint (hidden := true) "Try
  `rw [Matrix.diag_apply, Matrix.diagonal_apply_eq, Matrix.diag_apply, Matrix.diagonal_apply_eq, Matrix.diag_apply, Matrix.diagonal_apply_eq]`.
  This turns each term into `d 0`, `d 1`, `d 2`."
  rw [diag_apply, diagonal_apply_eq, diag_apply, diagonal_apply_eq, diag_apply, diagonal_apply_eq]
  Hint "The goal is now `d 0 + d 1 + d 2 = 10`. Substitute the known
  values using the hypotheses."
  Hint (hidden := true) "Try `rw [h0, h1, h2]`. The goal becomes
  `3 + 0 + 7 = 10`. Close with `ring`."
  rw [h0, h1, h2]
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
You computed a trace with actual numbers: `tr(diagonal d) = 3 + 0 + 7 = 10`.

The key new tool was `Fin.sum_univ_three`, which converts an abstract
sum over `Fin 3` into an explicit expression `f 0 + f 1 + f 2`. This
is the bridge between the summation machinery and concrete computation.

The full pipeline was:
1. `Fin.sum_univ_three` — expand the sum into three terms
2. `diag_apply` + `diagonal_apply_eq` — evaluate each summand
3. Substitute known values and compute

In practice, the trace of a matrix is how you compute important
quantities: the trace of a projection gives its rank, the trace of a
density matrix gives a probability, and the trace of the identity gives
the dimension of the space.
"

/-- `Fin.sum_univ_three` expands a sum over `Fin 3` into three terms:

`∑ i : Fin 3, f i = f 0 + f 1 + f 2`

## Syntax
```
rw [Fin.sum_univ_three]
```

## When to use it
When you need to evaluate a sum over `Fin 3` to a concrete expression.
Also available: `Fin.sum_univ_two` for `Fin 2`.

## Example
`rw [Fin.sum_univ_three]` turns `∑ i, d i = 10` into
`d 0 + d 1 + d 2 = 10`.
-/
TheoremDoc Fin.sum_univ_three as "Fin.sum_univ_three" in "Fin"

TheoremTab "Matrix"
NewTheorem Fin.sum_univ_three

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
