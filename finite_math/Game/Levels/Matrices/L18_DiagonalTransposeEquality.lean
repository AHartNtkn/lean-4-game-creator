import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 18

Title "Symmetric Matrices: Diagonal Transpose"

Introduction "
# Diagonal Matrices Are Symmetric

A matrix is **symmetric** if it equals its own transpose: $M = M^T$.
The transpose of a diagonal matrix is still the same diagonal matrix —
diagonal matrices are symmetric.

Why? On the diagonal (`i = j`), both `(diagonal d) i i` and
`(diagonal d)ᵀ i i` equal `d i`. Off the diagonal (`i ≠ j`), both
equal `0`. So every entry matches.

You know the tools: `ext i j`, `transpose_apply`, and
`obtain rfl | h := eq_or_ne i j` to split into cases. But after
peeling the transpose, the goal becomes
`(diagonal d) j i = (diagonal d) i j` — notice the indices are
**swapped**. The left side has `j i`, but your hypothesis says `i ≠ j`.

**Flipping inequalities**: When you have `h : i ≠ j` and need `j ≠ i`,
use `h.symm`. The `.symm` method on `Ne` (≠) flips the arguments:
if `h : i ≠ j` then `h.symm : j ≠ i`. This is needed because
`diagonal_apply_ne` expects a proof that the FIRST index differs from
the SECOND.

**Your task**: Prove that `(diagonal d)ᵀ = diagonal d`.
"

/-- The transpose of a diagonal matrix equals itself. -/
Statement (d : Fin 3 → ℤ) : (diagonal d)ᵀ = diagonal d := by
  Hint "You need to prove two matrices are equal. Start with `ext i j`."
  Hint (hidden := true) "Try `ext i j`."
  ext i j
  Hint "Peel off the transpose with `Matrix.transpose_apply`."
  Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`. The goal
  becomes `(diagonal d) j i = (diagonal d) i j`."
  rw [transpose_apply]
  Hint "The goal is `(diagonal d) j i = (diagonal d) i j`. Whether
  the diagonal entries match depends on whether `i = j`. Split into
  cases with `obtain rfl | h := eq_or_ne i j`."
  Hint (hidden := true) "Try `obtain rfl | h := eq_or_ne i j`.
  The `rfl` pattern automatically handles the `i = j` case (both
  sides become `(diagonal d) i i`). You are left with the `i ≠ j`
  case."
  obtain rfl | h := eq_or_ne i j
  -- i = j case: (diagonal d) i i = (diagonal d) i i, closed by rfl pattern
  · Hint "Both sides are `(diagonal d) i i`. This is `rfl`."
    rfl
  -- i ≠ j case
  · Hint "You have `h : i ≠ j`. Both sides are off-diagonal entries,
    so both equal `0`. Use `diagonal_apply_ne` twice — once with
    `h.symm` (for `j ≠ i`) on the left side, and once with `h`
    (for `i ≠ j`) on the right side."
    Hint (hidden := true) "Try
    `rw [Matrix.diagonal_apply_ne d h.symm, Matrix.diagonal_apply_ne d h]`."
    rw [diagonal_apply_ne d h.symm, diagonal_apply_ne d h]

Conclusion "
You proved that diagonal matrices are **symmetric** — they equal their
own transpose.

The proof used a case split on index equality. This is a fundamental
pattern for matrices: many matrix properties depend on whether you are
looking at a diagonal entry (`i = j`) or an off-diagonal entry
(`i ≠ j`). The `obtain rfl | h := eq_or_ne i j` move cleanly
separates these two worlds.

In linear algebra, symmetric matrices form one of the most important
classes: they have real eigenvalues, orthogonal eigenvectors, and are
diagonalizable. The fact that every diagonal matrix is symmetric is the
simplest example of this class.

But beware: **not every symmetric matrix is diagonal**. A matrix can be
symmetric (equal to its transpose) while having nonzero off-diagonal
entries. The next level will show you a concrete example.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_transpose Matrix.diag_diagonal Matrix.diag_transpose Matrix.diagonal_add Matrix.diagonal_apply
