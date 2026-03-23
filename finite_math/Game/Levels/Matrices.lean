import Game.Levels.Matrices.L01_MatricesAreFunctions
import Game.Levels.Matrices.L02_ConcreteMatrixEntries
import Game.Levels.Matrices.L03_TransposeEntries
import Game.Levels.Matrices.L04_MatrixExtensionality
import Game.Levels.Matrices.L05_DoubleTranspose
import Game.Levels.Matrices.L06_MatrixAddition
import Game.Levels.Matrices.L07_TransposeAddition
import Game.Levels.Matrices.L08_DiagonalOnDiag
import Game.Levels.Matrices.L09_DiagonalOffDiag
import Game.Levels.Matrices.L10_DiagOfDiagonal
import Game.Levels.Matrices.L11_DiagDiagonalCounterexample
import Game.Levels.Matrices.L12_TraceBigOp
import Game.Levels.Matrices.L13_ConcreteTrace
import Game.Levels.Matrices.L14_TransposeDiagonalEntries
import Game.Levels.Matrices.L15_TraceOfTranspose
import Game.Levels.Matrices.L16_TraceLinearity
import Game.Levels.Matrices.L17_DiagonalAddition
import Game.Levels.Matrices.L18_DiagonalTransposeEquality
import Game.Levels.Matrices.L19_SymmetricCounterexample
import Game.Levels.Matrices.L20_Boss

World "Matrices"
Title "Matrices"

Introduction "
# Matrices: Functions of Two Indices

Matrices are everywhere in mathematics: they represent linear maps
between vector spaces, systems of linear equations, adjacency
structures in graphs, and data tables in statistics. They are the
central computational tool of linear algebra.

In Lean, a matrix is nothing more than a **function of two indices**.

A `Matrix (Fin m) (Fin n) α` is literally `Fin m → Fin n → α`. Entry
`(i, j)` is accessed by `M i j` — double function application. The
first index selects the row, the second selects the column.

This world teaches you to:
- **Build** matrices using `Matrix.of` from functions
- **Access** entries using `M i j` and `Matrix.of_apply`
- **Add**: `(M + N) i j = M i j + N i j` via `Matrix.add_apply`
- **Transpose**: `Mᵀ i j = M j i` via `Matrix.transpose_apply`
- **Prove equality**: `ext i j` reduces matrix equality to entry equality
- **Diagonal matrices**: `diagonal d` has `d i` on the diagonal and `0`
  off it, via `diagonal_apply_eq` and `diagonal_apply_ne`
- **Extract diagonals**: `diag M i = M i i` via `diag_apply`
- **Connect to big operators**: the trace `∑ i, diag M i` bridges
  matrices to the summation machinery from earlier worlds
- **Combine** these tools to prove properties of structured matrices

The central insight is that matrices ARE functions. Every matrix fact
is a statement about indices. Every matrix proof is an exercise in
function reasoning — the same reasoning you used for tuples in an
earlier world, now applied to functions of two arguments.
"
