import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 5

Title "Double Transpose"

Introduction "
# Transposing Twice Returns the Original

If you transpose a matrix and then transpose the result, you get back
the original matrix. This makes intuitive sense: swapping rows and
columns twice undoes itself.

Formally: $M^{TT} = M$, or in Lean: `Mᵀᵀ = M`.

You now have the tools to prove this:
1. `ext i j` — reduce matrix equality to entry-wise equality
2. `Matrix.transpose_apply` — evaluate a transpose entry

**Your task**: Prove that transposing twice is the identity.
"

/-- Transposing a matrix twice gives back the original. -/
Statement (M : Matrix (Fin 2) (Fin 2) ℤ) : Mᵀᵀ = M := by
  Hint "You need to prove two matrices are equal. Start with `ext i j`."
  Hint (hidden := true) "Try `ext i j`."
  ext i j
  Hint "The goal is `Mᵀᵀ i j = M i j`. The outer transpose swaps the
  indices: `Mᵀᵀ i j = Mᵀ j i`. Rewrite with `Matrix.transpose_apply`
  to peel off the outer transpose."
  Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`. The goal
  becomes `Mᵀ j i = M i j`."
  rw [transpose_apply]
  Hint "Now `Mᵀ j i` — the inner transpose swaps again: `Mᵀ j i = M i j`.
  Rewrite with `Matrix.transpose_apply` once more."
  Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`."
  rw [transpose_apply]

Conclusion "
Each `rw [Matrix.transpose_apply]` peeled off one layer of transpose:

$$M^{TT}\\,i\\,j \\xrightarrow{\\text{transpose\\_apply}} M^T\\,j\\,i \\xrightarrow{\\text{transpose\\_apply}} M\\,i\\,j$$

Swapping twice restores the original order. This is a general fact
about involutions: any function that is its own inverse satisfies
`f (f x) = x`.

**The 'peel' strategy**: This proof introduced a pattern you will use
repeatedly in this world. When you have nested matrix operations
(like `Mᵀᵀ`), rewrite with the **outermost** operation's lemma first
to simplify the outer layer, then rewrite again to handle the next
layer. Each `rw` peels off one operation. You will see this same
layer-by-layer simplification when combining transpose with diagonal
matrices later.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.transpose_transpose
