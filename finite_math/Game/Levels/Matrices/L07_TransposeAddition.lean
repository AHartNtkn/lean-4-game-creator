import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 7

Title "Transpose Distributes Over Addition"

Introduction "
# Combining Transpose and Addition

You now know two matrix operations — **transpose** (`Mᵀ`) and
**addition** (`M + N`) — and their entry-level lemmas:
- `Matrix.transpose_apply : Mᵀ i j = M j i`
- `Matrix.add_apply : (M + N) i j = M i j + N i j`

A natural question: how do they interact? The answer is that
transposing a sum equals the sum of the transposes:

$$(M + N)^T = M^T + N^T$$

The proof uses `ext i j` to reduce to entries, then the peel strategy:
rewrite with the outermost operation's lemma, then simplify layer by
layer.

**Your task**: Prove that transpose distributes over addition.
"

/-- Transpose distributes over matrix addition. -/
Statement (M N : Matrix (Fin 2) (Fin 2) ℤ) : (M + N)ᵀ = Mᵀ + Nᵀ := by
  Hint "You need to prove two matrices are equal. Start with `ext i j`."
  Hint (hidden := true) "Try `ext i j`."
  ext i j
  Hint "Now simplify each side using the entry-level lemmas. The left
  side has a transpose of a sum — peel the transpose first, then
  expand the addition. The right side has a sum of transposes —
  expand the addition, then peel each transpose."
  Hint (hidden := true) "Start with `rw [Matrix.transpose_apply]` to peel
  the outer transpose on the left. Then `rw [Matrix.add_apply]` to expand
  the sum (this hits both sides). Then `rw [Matrix.add_apply]` again for
  the remaining sum. Then `rw [Matrix.transpose_apply]` twice more for
  the transposes on the right. Each `rw` peels one layer."
  rw [transpose_apply, add_apply, add_apply, transpose_apply, transpose_apply]

Conclusion "
The proof used four rewrites in a chain:

1. `transpose_apply` peeled the outer transpose on the left:
   $(M + N)^T\\,i\\,j \\to (M + N)\\,j\\,i$
2. `add_apply` expanded both sums:
   $M\\,j\\,i + N\\,j\\,i = M^T\\,i\\,j + N^T\\,i\\,j$
3. `transpose_apply` simplified the remaining transposes on the right:
   $M^T\\,i\\,j + N^T\\,i\\,j \\to M\\,j\\,i + N\\,j\\,i$

The key insight: since `rw` replaces ALL occurrences of a pattern,
one `rw [Matrix.add_apply]` can expand both sides at once, and one
`rw [Matrix.transpose_apply]` can simplify both transposes on the
right. The peel strategy scales naturally when operations are nested.

This is your first result combining two operations, and you will see
this pattern again: prove a matrix identity by reducing both sides
to the same entry-level expression via chained rewrites.

**Alternative strategy**: After `ext i j`, you could expand both sides
fully with rewrites until the goal is a pure integer expression, then
close with `ring`. The 'expand then ring' approach works whenever both
sides reduce to the same algebraic expression over entries.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.transpose_add
