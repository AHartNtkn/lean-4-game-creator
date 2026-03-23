import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 12

Title "Trace: Connecting Diagonal to Big Operators"

Introduction "
# The Trace of a Diagonal Matrix

The **trace** of a square matrix is the sum of its diagonal entries:

$$\\text{tr}(M) = \\sum_i M_{ii} = \\sum_i \\text{diag}\\,M\\,i$$

In Lean, this is `∑ i ∈ Finset.univ, diag M i`.

You already know that `diag (diagonal d) = d` — extracting the diagonal
of a diagonal matrix recovers the original function. This means:

$$\\text{tr}(\\text{diagonal}\\,d) = \\sum_i d\\,i$$

The trace of a diagonal matrix is just the sum of the diagonal values.

To prove this, you need a tool from the big operator worlds:
`Finset.sum_congr rfl`. It says: if you can show that corresponding
summands are equal for each index, then the sums are equal. You used
this in the Big Operator Algebra and Binomial Theorem worlds.

**Your task**: Prove that the trace of `diagonal d` equals `∑ i, d i`.
"

/-- The trace of a diagonal matrix equals the sum of the diagonal values. -/
Statement (d : Fin 3 → ℤ) :
    ∑ i ∈ Finset.univ, diag (diagonal d) i = ∑ i ∈ Finset.univ, d i := by
  Hint "The two sums range over the same finset (`Finset.univ`).
  You need to show the summands are equal for each index. Use
  `Finset.sum_congr rfl` to reduce to a pointwise argument."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl`. This
  creates a goal: for each `i ∈ Finset.univ`, show
  `diag (diagonal d) i = d i`."
  apply Finset.sum_congr rfl
  Hint "Now introduce the index `i` and the membership proof."
  Hint (hidden := true) "Try `intro i _`."
  intro i _
  Hint "The goal is `diag (diagonal d) i = d i`. Use the chained
  rewrite from Level 9: `diag_apply` peels `diag`, then
  `diagonal_apply_eq` evaluates the on-diagonal entry."
  Hint (hidden := true) "Try
  `rw [Matrix.diag_apply, Matrix.diagonal_apply_eq]`."
  rw [diag_apply, diagonal_apply_eq]

Conclusion "
You connected matrices to big operators. The proof used
`Finset.sum_congr rfl` to reduce a sum equality to a pointwise
argument, then `diag_apply` and `diagonal_apply_eq` to simplify
each summand.

The **trace** is one of the most important invariants in linear
algebra. It satisfies remarkable properties:
- `tr(A + B) = tr(A) + tr(B)` — the trace is linear (you will prove
  this soon)
- `tr(AB) = tr(BA)` — the trace is cyclic (even when `AB ≠ BA`)
- The trace of a projection is its rank

What you proved here — `tr(diagonal d) = ∑ i, d i` — is the starting
point. The diagonal entries of a matrix encode its most important
spectral information, and summing them (the trace) captures a key
piece of that information.

This level bridges the matrix world to the big operator machinery
you built in earlier worlds — specifically, you used
`Finset.sum_congr rfl` from the Big Operator Algebra world to
reduce a sum equality to pointwise equality of summands.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
