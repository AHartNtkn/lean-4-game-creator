import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 6

Title "Matrix Addition Is Entry-wise"

Introduction "
# Adding Matrices

Since matrices are functions of two indices, matrix addition is
**entry-wise**: each entry of `M + N` is the sum of the corresponding
entries of `M` and `N`. The key lemma is:

```
Matrix.add_apply : (M + N) i j = M i j + N i j
```

This is a direct consequence of the fact that matrices ARE functions.
Function addition in Lean is pointwise: `(f + g) x = f x + g x`.
For matrices (functions of two arguments), you get
`(M + N) i j = M i j + N i j`.

This might seem trivially obvious — of course matrix addition is
entry-wise. But the point is deeper: in Lean, this is not a
definition you need to memorize, it is a CONSEQUENCE of the fact
that matrices are functions. The algebraic structure of matrices
is inherited directly from the algebraic structure of entries.

**Your task**: Given specific values for individual matrix entries,
compute the entry of the sum.
"

/-- Entry-wise addition of matrices. -/
Statement (M N : Matrix (Fin 2) (Fin 2) ℤ) (hM : M 0 1 = 3) (hN : N 0 1 = 2) :
    (M + N) 0 1 = 5 := by
  Hint "The goal asks about entry `(0, 1)` of the sum `M + N`.
  Rewrite with `Matrix.add_apply` to split this into the sum of
  individual entries."
  Hint (hidden := true) "Try `rw [Matrix.add_apply]`."
  rw [add_apply]
  Hint "Now the goal is `M 0 1 + N 0 1 = 5`. You know the individual
  entries from your hypotheses `hM` and `hN`. Rewrite with both to
  substitute the concrete values."
  Hint (hidden := true) "Try `rw [hM, hN]`. The goal becomes `3 + 2 = 5`."
  rw [hM, hN]
  Hint (hidden := true) "The goal is `3 + 2 = 5`. Try `ring` or `omega`."
  ring

Conclusion "
One rewrite — that is all it takes. `Matrix.add_apply` says that
reading an entry of `M + N` is the same as reading the entries of
`M` and `N` separately, then adding.

This is the 'matrices are functions' thesis at its most powerful.
Matrix addition is not a separate concept that needs its own rules —
it is just function addition, which is just pointwise addition of
values. Everything about matrix algebra follows from the fact that
matrices are functions of two indices.

The same principle applies to other operations: subtraction is
entry-wise, scalar multiplication is entry-wise, and the zero
matrix is the function that returns `0` at every entry. The
exceptions — matrix multiplication and transpose — are the
interesting ones precisely because they mix entries from different
positions.
"

/-- `Matrix.add_apply` evaluates entry-wise addition:

`(M + N) i j = M i j + N i j`

## Syntax
```
rw [Matrix.add_apply]       -- in the goal
rw [Matrix.add_apply] at h  -- in a hypothesis
```

## When to use it
When the goal or a hypothesis contains `(M + N) i j` and you want
to split it into `M i j + N i j`.

## Example
`rw [Matrix.add_apply]` turns `(M + N) 0 1 = 5` into
`M 0 1 + N 0 1 = 5`.
-/
TheoremDoc Matrix.add_apply as "Matrix.add_apply" in "Matrix"

TheoremTab "Matrix"
NewTheorem Matrix.add_apply

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
