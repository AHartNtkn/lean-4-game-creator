import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 10

Title "Extracting the Diagonal"

Introduction "
# The Diag Function

`Matrix.diag` extracts the diagonal entries of a square matrix as a
function:

```
Matrix.diag_apply : Matrix.diag M i = M i i
```

This is the inverse operation to `Matrix.diagonal`: while `diagonal`
builds a matrix from diagonal values, `diag` reads the diagonal values
from a matrix.

If you build a diagonal matrix from `d` and then extract the diagonal,
you should get `d` back. Proving this requires combining `ext`,
`Matrix.diag_apply`, and `Matrix.diagonal_apply_eq`.

**Chained rewrites**: When you need to apply two rewrites in sequence,
you can write `rw [A, B]` instead of `rw [A]` followed by `rw [B]`.
This applies `A` first, then `B`, in a single tactic call. This is
especially natural with the 'peel' strategy — each comma peels one
more layer.

**Your task**: Prove that `diag (diagonal d) = d`.
"

/-- Extracting the diagonal of a diagonal matrix recovers the original function. -/
Statement (d : Fin 3 → ℤ) : diag (diagonal d) = d := by
  Hint "You need to prove two functions are equal. Use `ext i` to
  reduce to a pointwise statement."
  Hint (hidden := true) "Try `ext i`. The goal becomes
  `diag (diagonal d) i = d i`."
  ext i
  Hint "Now unfold `diag` using `Matrix.diag_apply`. This says
  `diag M i = M i i`."
  Hint (hidden := true) "Try `rw [Matrix.diag_apply]`. The goal becomes
  `(diagonal d) i i = d i`."
  rw [diag_apply]
  Hint "The goal is now `(diagonal d) i i = d i` — an on-diagonal entry.
  You know this one. You could also have done both rewrites in one step
  with `rw [Matrix.diag_apply, Matrix.diagonal_apply_eq]`."
  Hint (hidden := true) "Try `rw [Matrix.diagonal_apply_eq]`."
  rw [diagonal_apply_eq]

Conclusion "
The proof combined three moves:

1. `ext i` — reduced function equality to pointwise equality
2. `diag_apply` — unfolded `diag` to raw entry access `M i i`
3. `diagonal_apply_eq` — evaluated the diagonal matrix on the diagonal

Steps 2 and 3 are a natural chained rewrite:
`rw [Matrix.diag_apply, Matrix.diagonal_apply_eq]` peels both layers
in one tactic call.

This is a mini-integration: `diag` and `diagonal` are inverse
operations on the diagonal values. Building a diagonal matrix and
reading its diagonal gives back the original function.

**Important**: This result goes in ONE direction only: `diag (diagonal d) = d`.
The reverse — `diagonal (diag M) = M` — is NOT true in general.
`diagonal (diag M)` keeps only the diagonal entries of `M` and sets
everything else to zero. If `M` has any nonzero off-diagonal entries,
they are lost. So `diag` and `diagonal` are not full inverses; `diag`
is a left inverse of `diagonal`, but not a right inverse.

In linear algebra, `diag M` feeds directly into `∑ i, diag M i`
(the **trace** of `M`), connecting diagonal extraction to the
big-operator machinery from earlier worlds. The relationship
`diag (diagonal d) = d` is the starting point for these applications.
"

/-- `Matrix.diag_apply` evaluates the diagonal extraction:

`Matrix.diag M i = M i i`

## Syntax
```
rw [Matrix.diag_apply]
```

## When to use it
When the goal contains `Matrix.diag M i` and you want to
replace it with `M i i`.

## Example
`rw [Matrix.diag_apply]` turns `diag M 2 = 5` into `M 2 2 = 5`.
-/
TheoremDoc Matrix.diag_apply as "Matrix.diag_apply" in "Matrix"

/-- `Matrix.diag M` extracts the diagonal of a square matrix `M` as a
function: `diag M i = M i i`.

## Syntax
```
Matrix.diag M     -- the diagonal function
Matrix.diag M i   -- the i-th diagonal entry
```

## Key lemma
`Matrix.diag_apply : diag M i = M i i`
-/
DefinitionDoc Matrix.diag as "Matrix.diag"

TheoremTab "Matrix"
NewTheorem Matrix.diag_apply
NewDefinition Matrix.diag

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
