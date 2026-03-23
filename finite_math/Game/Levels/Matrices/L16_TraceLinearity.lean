import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 16

Title "Trace Is Additive"

Introduction "
# Trace Distributes Over Addition

In Level 12 you computed the trace of a diagonal matrix, and in
Level 15 you proved that the trace is invariant under transpose.
Now you will prove another fundamental property:

$$\\text{tr}(M + N) = \\text{tr}(M) + \\text{tr}(N)$$

The trace is **linear**: the trace of a sum is the sum of the traces.

Why? Because `diag (M + N) i = (M + N) i i = M i i + N i i = diag M i + diag N i`.
Each diagonal entry of the sum is the sum of the diagonal entries.
Summing over all indices preserves this.

The proof uses two tools:
- `Finset.sum_add_distrib` to split a sum of sums: `∑ i, (f i + g i) = ∑ i, f i + ∑ i, g i`
- `Finset.sum_congr rfl` to show each summand matches

**Your task**: Prove trace linearity.
"

/-- The trace distributes over matrix addition. -/
Statement (M N : Matrix (Fin 3) (Fin 3) ℤ) :
    ∑ i ∈ Finset.univ, diag (M + N) i =
    ∑ i ∈ Finset.univ, diag M i + ∑ i ∈ Finset.univ, diag N i := by
  Hint "The right side is a sum of two separate sums. Use
  `← Finset.sum_add_distrib` to combine them into a single sum
  `∑ i, (diag M i + diag N i)`, then show the summands match."
  Hint (hidden := true) "Try `rw [← Finset.sum_add_distrib]`.
  This rewrites the right side from `∑ f + ∑ g` to `∑ (f + g)`."
  rw [← Finset.sum_add_distrib]
  Hint "Now both sides are sums over `Finset.univ`. Use
  `Finset.sum_congr rfl` to reduce to showing each summand is equal."
  Hint (hidden := true) "Try `apply Finset.sum_congr rfl` then `intro i _`."
  apply Finset.sum_congr rfl
  intro i _
  Hint "The goal is `diag (M + N) i = diag M i + diag N i`. Unfold
  `diag` with `diag_apply`, then expand the addition with `add_apply`.
  Each `diag_apply` rewrite turns `diag X i` into `X i i`."
  Hint (hidden := true) "Try
  `rw [Matrix.diag_apply, Matrix.add_apply, Matrix.diag_apply, Matrix.diag_apply]`."
  rw [diag_apply, add_apply, diag_apply, diag_apply]

Conclusion "
You proved that the trace is **linear**: `tr(M + N) = tr(M) + tr(N)`.

The proof combined two tools:
1. `← Finset.sum_add_distrib` collapsed `∑ f + ∑ g` into `∑ (f + g)`
2. `sum_congr rfl` + entry-level rewrites showed each summand matches

Together with transpose-invariance (Level 15), you now have two of the
three fundamental trace properties:
- **Linearity**: `tr(A + B) = tr(A) + tr(B)`
- **Transpose-invariance**: `tr(Aᵀ) = tr(A)`
- **Cyclicity**: `tr(AB) = tr(BA)` (not covered here — it requires
  matrix multiplication)

The trace is **additive**: it sends a matrix to a number (the sum of
its diagonal entries) in a way that respects addition. Full linearity
also requires scalar homogeneity (`tr(c * M) = c * tr(M)`), which we
have not proven here. But additivity alone makes the trace one of the
most important tools in linear algebra, spectral theory, and quantum
mechanics.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
