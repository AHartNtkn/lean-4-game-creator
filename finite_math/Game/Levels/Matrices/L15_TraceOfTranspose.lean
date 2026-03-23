import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 15

Title "Trace of a Transpose"

Introduction "
# The Trace Is Transpose-Invariant

The trace of a matrix is the sum of its diagonal entries:
$\\text{tr}(M) = \\sum_i M_{ii}$. In Level 12 you computed the trace
of a diagonal matrix. Now you will prove a key property:

$$\\text{tr}(M^T) = \\text{tr}(M)$$

The trace of a transpose equals the trace of the original matrix.

Why? Because the $i$-th diagonal entry of $M^T$ is $M^T_{ii} = M_{ii}$
— transposing swaps rows and columns, but diagonal entries have
the same row and column index, so they do not move.

The proof uses `Finset.sum_congr rfl` (from Level 12) to reduce to
showing each summand is equal, then `diag_apply` and
`transpose_apply` to simplify.

**Your task**: Prove that `tr(Mᵀ) = tr(M)`.
"

/-- The trace of a transpose equals the trace of the original matrix. -/
Statement (M : Matrix (Fin 3) (Fin 3) ℤ) :
    ∑ i ∈ Finset.univ, diag Mᵀ i = ∑ i ∈ Finset.univ, diag M i := by
  Hint "The two sums range over the same finset. Use
  `Finset.sum_congr rfl` to reduce to showing the summands are
  equal for each index."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl` then
  `intro i _`."
  apply Finset.sum_congr rfl
  intro i _
  Hint "The goal is `diag Mᵀ i = diag M i`. Unfold `diag` with
  `diag_apply`, then peel the transpose with `transpose_apply`."
  Hint (hidden := true) "Try
  `rw [Matrix.diag_apply, Matrix.transpose_apply, Matrix.diag_apply]`."
  rw [diag_apply, transpose_apply, diag_apply]

Conclusion "
The proof was short: `diag_apply` unfolded both `diag` applications
to raw entries, and `transpose_apply` showed that $M^T_{ii} = M_{ii}$.

This is a fundamental property of the trace. Together with linearity
(`tr(A + B) = tr(A) + tr(B)`) and the cyclic property
(`tr(AB) = tr(BA)`), transpose-invariance is one of the three
defining features that make the trace useful throughout linear algebra.

The proof technique — `sum_congr rfl` to reduce a sum equality to
pointwise equality of summands — is the same one you used in Level 12.
It works whenever two sums range over the same finset and you want
to show corresponding terms are equal.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
