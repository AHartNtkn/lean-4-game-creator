import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 2

Title "Reading a Concrete Matrix"

Introduction "
# A Matrix with Visible Entries

In the previous level you applied `Matrix.of_apply` to an abstract
function `f`. Let's now see a **concrete** matrix — one with actual
numbers.

The matrix `Matrix.of ![![3, 1], ![0, 7]]` is a 2×2 integer matrix
built from two row vectors:

$$\\begin{pmatrix} 3 & 1 \\\\\\\\ 0 & 7 \\end{pmatrix}$$

Here `![![3, 1], ![0, 7]]` is a function `Fin 2 → Fin 2 → ℤ`:
- Row 0 is `![3, 1]`, so `f 0 0 = 3` and `f 0 1 = 1`
- Row 1 is `![0, 7]`, so `f 1 0 = 0` and `f 1 1 = 7`

Notice this matrix is NOT diagonal — it has a nonzero entry at
position `(0, 1)`. Not all matrices are diagonal; `diagonal` is a
special construction.

**Your task**: Read entry `(1, 0)` of this matrix using `Matrix.of_apply`.
"

/-- Read a specific entry from a concrete matrix. -/
Statement : Matrix.of ![![(3 : ℤ), 1], ![0, 7]] 1 0 = 0 := by
  Hint "The goal asks for entry `(1, 0)` of the matrix. Use
  `Matrix.of_apply` to unwrap `Matrix.of`, reducing the matrix
  access to raw function application."
  Hint (hidden := true) "Try `rw [Matrix.of_apply]`."
  rw [of_apply]
  Hint "The matrix wrapper is gone. Lean now sees the concrete
  function `![![3, 1], ![0, 7]]` applied to indices `1` and `0`.
  Both sides are equal by computation — use `rfl`."
  Hint (hidden := true) "Try `rfl`."
  rfl

Conclusion "
After `rw [Matrix.of_apply]`, the matrix wrapper is removed and Lean
sees the raw function `![![3, 1], ![0, 7]]` applied to indices `1`
and `0`. It evaluates row 1 (`![0, 7]`), then column 0 (`0`), giving
the result directly.

This is the 'matrices are functions' thesis in action: a concrete
matrix is just a function from index pairs to values, and reading
an entry is just function application. Every matrix operation you
learn in this world — transpose, diagonal, extensionality — ultimately
reduces to manipulating these function applications.
"

TheoremTab "Matrix"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
