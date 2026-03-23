import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 14

Title "Transpose + Diagonal: Coached Practice"

Introduction "
# Combining Transpose and Diagonal

You will recognize the **peel strategy** from Level 5: when you have
nested matrix operations, rewrite with the outermost operation's lemma
first to simplify layer by layer.

Here you can read entries of a transposed diagonal matrix by applying
`transpose_apply` first (to swap the indices) and then
`diagonal_apply_eq` or `diagonal_apply_ne` (to evaluate the
diagonal matrix).

**Your task**: Given a diagonal function `d` with `d 1 = 5`, prove
two things about the transpose of `diagonal d`:
1. The off-diagonal entry `(diagonal d)ᵀ 1 2` is `0`.
2. The on-diagonal entry `(diagonal d)ᵀ 1 1` is `5`.

**Aside**: You have been using `constructor` to split `P ∧ Q` into
two goals. There is a more flexible alternative — `refine ⟨?_, ?_⟩` —
where each `?_` becomes a separate subgoal. For a 2-way conjunction
this is equivalent to `constructor`, but `refine` scales to any number
of parts. We will stick with `constructor` here.
"

/-- Evaluate entries of a transposed diagonal matrix. -/
Statement (d : Fin 3 → ℤ) (hd : d 1 = 5) :
    (diagonal d)ᵀ 1 2 = 0 ∧ (diagonal d)ᵀ 1 1 = 5 := by
  Hint "Split the conjunction into two parts."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: off-diagonal entry of transpose
  · Hint "**Part 1**: The goal is `(diagonal d)ᵀ 1 2 = 0`. Peel off the
    transpose — this is the peel strategy from Level 5."
    Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`. The goal
    becomes `(diagonal d) 2 1 = 0`."
    rw [transpose_apply]
    Hint "Now you have an off-diagonal entry of a diagonal matrix.
    The indices `2` and `1` are different."
    Hint (hidden := true) "Try `exact Matrix.diagonal_apply_ne d (by omega)`."
    exact diagonal_apply_ne d (by omega)
  -- Part 2: on-diagonal entry of transpose
  · Hint "**Part 2**: The goal is `(diagonal d)ᵀ 1 1 = 5`. Again,
    peel off the transpose."
    Hint (hidden := true) "Try `rw [Matrix.transpose_apply]`. The goal
    becomes `(diagonal d) 1 1 = 5`."
    rw [transpose_apply]
    Hint "Now you have an on-diagonal entry. Evaluate it with
    `diagonal_apply_eq`."
    Hint (hidden := true) "Try `rw [Matrix.diagonal_apply_eq]`. The goal
    becomes `d 1 = 5`."
    rw [diagonal_apply_eq]
    Hint "Now use the hypothesis."
    Hint (hidden := true) "Try `exact hd`."
    exact hd

Conclusion "
Reading entries of `(diagonal d)ᵀ` is a two-step peel:

1. `transpose_apply` to swap the indices: `(diagonal d)ᵀ i j` becomes
   `(diagonal d) j i`
2. `diagonal_apply_eq` or `diagonal_apply_ne` depending on whether
   `j = i` or `j ≠ i`

The transpose of a diagonal matrix is still diagonal — transposing
doesn't move entries on the main diagonal, and zeros stay zero.

"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_transpose Matrix.diagonal_apply
