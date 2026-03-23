import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 19

Title "Symmetric Does Not Mean Diagonal"

Introduction "
# A Symmetric Matrix That Is Not Diagonal

In the previous level, you proved that every diagonal matrix is
symmetric: `(diagonal d)ᵀ = diagonal d`. You might wonder: is
every symmetric matrix also diagonal?

The answer is **no**. Here is a concrete counterexample:

$$M = \\begin{pmatrix} 1 & 2 \\\\\\\\ 2 & 3 \\end{pmatrix}$$

This matrix is symmetric because `M 0 1 = M 1 0 = 2` (the
off-diagonal entries match when you transpose). But it is NOT
diagonal because the off-diagonal entry `M 0 1 = 2` is nonzero.

A diagonal matrix has ALL off-diagonal entries equal to `0`. A
symmetric matrix only requires that entry `(i, j)` equals entry
`(j, i)` — the off-diagonal entries can be anything, as long as
they mirror across the main diagonal.

**Your task**: Prove both facts about this concrete matrix.
"

/-- A matrix can be symmetric (matching off-diagonal entries) but not diagonal
(nonzero off-diagonal entry). -/
Statement :
    Matrix.of ![![(1 : ℤ), 2], ![2, 3]] 0 1 = Matrix.of ![![(1 : ℤ), 2], ![2, 3]] 1 0
    ∧ Matrix.of ![![(1 : ℤ), 2], ![2, 3]] 0 1 ≠ 0 := by
  Hint "Split the conjunction into two parts."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: symmetric (matching off-diagonal)
  · Hint "**Part 1**: Show that the off-diagonal entries match.
    Unwrap both `Matrix.of` expressions with `rw [Matrix.of_apply]`
    (you need it twice — once for each side). Both entries evaluate
    to the same value."
    Hint (hidden := true) "Try `rw [Matrix.of_apply, Matrix.of_apply]`.
    Each `of_apply` unwraps one `Matrix.of`, and the resulting
    concrete values are equal."
    rw [of_apply, of_apply]
    rfl
  -- Part 2: not diagonal (nonzero off-diagonal)
  · Hint "**Part 2**: Show that the off-diagonal entry is not zero.
    Unwrap with `Matrix.of_apply` to evaluate the concrete entry."
    Hint "After `rw [Matrix.of_apply]`, the vector notation
    `![![1, 2], ![2, 3]] 0 1` evaluates to `2`. The goal becomes
    `(2 : ℤ) ≠ 0`. Use `show (2 : ℤ) ≠ 0` to make this explicit,
    then `omega` closes it."
    Hint (hidden := true) "Try `rw [Matrix.of_apply]` then
    `show (2 : ℤ) ≠ 0` then `omega`."
    rw [of_apply]
    show (2 : ℤ) ≠ 0
    omega

Conclusion "
The matrix `![![1, 2], ![2, 3]]` is symmetric but not diagonal:
- **Symmetric**: `M 0 1 = 2 = M 1 0` — the off-diagonal entries mirror.
- **Not diagonal**: `M 0 1 = 2 ≠ 0` — there IS a nonzero off-diagonal entry.

This is important to remember:
- **Diagonal** ⟹ **Symmetric** (Level 18 proved this)
- **Symmetric** ⟹ **Diagonal** is FALSE (this level showed it)

The set of diagonal matrices is a proper SUBSET of the set of symmetric
matrices. Symmetric matrices are a much richer class — they include
correlation matrices, covariance matrices, Laplacian matrices in graph
theory, and many more. All diagonal matrices are symmetric, but most
symmetric matrices are not diagonal.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_transpose Matrix.diag_diagonal Matrix.diag_transpose Matrix.diagonal_add Matrix.diagonal_apply
