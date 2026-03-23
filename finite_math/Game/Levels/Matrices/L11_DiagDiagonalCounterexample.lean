import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 11

Title "Round-Tripping Loses Off-Diagonal Entries"

Introduction "
# Left Inverse Is Not Right Inverse

In Level 10, you proved that `diag (diagonal d) = d` — extracting the
diagonal of a diagonal matrix recovers the original function. The
conclusion warned that the reverse, `diagonal (diag M) = M`, is NOT
true in general.

Now you will prove this with a **concrete counterexample**.

Consider the matrix from Level 2:

$$M = \\begin{pmatrix} 3 & 1 \\\\\\\\ 0 & 7 \\end{pmatrix}$$

If you build `diagonal (diag M)`, you keep the diagonal entries (3 and 7)
but **set all off-diagonal entries to zero**. So the off-diagonal entry
at position `(0, 1)` goes from `1` in `M` to `0` in `diagonal (diag M)`.

**Your task**: Prove both facts:
1. The round-tripped matrix has `0` at position `(0, 1)` (the
   off-diagonal entry is lost).
2. The original matrix has `1` at position `(0, 1)` (the entry was
   nonzero to begin with).

Together these show that `diagonal (diag M) ≠ M` for this matrix.
"

/-- Round-tripping through diag then diagonal loses off-diagonal information. -/
Statement :
    (diagonal (diag (Matrix.of ![![(3 : ℤ), 1], ![0, 7]]))) 0 1 = 0
    ∧ (Matrix.of ![![(3 : ℤ), 1], ![0, 7]]) 0 1 = 1 := by
  Hint "Split the conjunction into two parts."
  Hint (hidden := true) "Try `constructor`."
  constructor
  -- Part 1: off-diagonal entry of diagonal (diag M) is 0
  · Hint "**Part 1**: The entry `(0, 1)` of `diagonal (diag M)` is
    off-diagonal (since `0 ≠ 1`). What do you know about off-diagonal
    entries of diagonal matrices?"
    Hint (hidden := true) "Establish that `0 ≠ 1` with
    `have h : (0 : Fin 2) ≠ 1 := by omega`, then use
    `exact Matrix.diagonal_apply_ne _ h`."
    have h : (0 : Fin 2) ≠ 1 := by omega
    exact diagonal_apply_ne _ h
  -- Part 2: M 0 1 = 1
  · Hint "**Part 2**: Evaluate the concrete matrix entry at `(0, 1)`.
    Unwrap `Matrix.of` with `of_apply` to see the raw vector notation."
    Hint (hidden := true) "Try `rw [Matrix.of_apply]` then `rfl`. The vector
    `![![3, 1], ![0, 7]]` at indices `0`, `1` evaluates to `1`."
    rw [of_apply]
    rfl

Conclusion "
You proved that `diagonal (diag M)` and `M` differ at entry `(0, 1)`:
- `diagonal (diag M) 0 1 = 0` — the round-trip zeroed out the off-diagonal
- `M 0 1 = 1` — but the original entry was nonzero

This means `diagonal ∘ diag` is NOT the identity function on matrices.
It is a **projection**: it keeps the diagonal and discards everything else.

Contrast this with Level 10, where you proved `diag ∘ diagonal = id`.
The pair `(diagonal, diag)` satisfies:
- `diag` is a **left inverse** of `diagonal`: `diag (diagonal d) = d`
- `diag` is NOT a **right inverse** of `diagonal`: `diagonal (diag M) ≠ M`
  in general

This asymmetry is a fundamental pattern: a function can have a left
inverse without having a right inverse. It happens whenever the function
is injective but not surjective — `diagonal` embeds the space of
diagonal functions into the larger space of all matrices, and `diag`
retracts back, but the retraction loses the off-diagonal information.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_apply
