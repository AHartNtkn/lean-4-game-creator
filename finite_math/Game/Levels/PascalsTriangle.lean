import Game.Levels.PascalsTriangle.L01_ComputeAnEntry
import Game.Levels.PascalsTriangle.L02_SymmetryInAction
import Game.Levels.PascalsTriangle.L03_MeetAntidiagonal
import Game.Levels.PascalsTriangle.L04_AntidiagonalNonMembership
import Game.Levels.PascalsTriangle.L05_AntidiagonalFacts
import Game.Levels.PascalsTriangle.L06_AntidiagonalMembership
import Game.Levels.PascalsTriangle.L07_RowSumViaAntidiagonal
import Game.Levels.PascalsTriangle.L08_SymmetricRowSum
import Game.Levels.PascalsTriangle.L09_SwapPractice
import Game.Levels.PascalsTriangle.L10_ConcreteVandermonde
import Game.Levels.PascalsTriangle.L11_Convolution
import Game.Levels.PascalsTriangle.L12_PascalFromVandermonde
import Game.Levels.PascalsTriangle.L13_TheCircleCloses
import Game.Levels.PascalsTriangle.L14_SymmetryOnAntidiagonal
import Game.Levels.PascalsTriangle.L15_SquaredBinomials
import Game.Levels.PascalsTriangle.L16_Boss

World "PascalsTriangle"
Title "Pascal's Triangle"

Introduction "
# Pascal's Triangle

Pascal's triangle is the most famous triangular array in mathematics:
```
          1
         1 1
        1 2 1
       1 3 3 1
      1 4 6 4 1
     1 5 10 10 5 1
```

Each entry is a binomial coefficient $\\binom{n}{k}$. Each interior
entry is the sum of the two above it (Pascal's identity). Each row
is symmetric ($\\binom{n}{k} = \\binom{n}{n-k}$). The sum of each
row is $2^n$.

You have already proved all these properties. In this world, you
will look at the triangle from a **new angle**: the **antidiagonal**.

The $n$-th antidiagonal is the set of all pairs $(i, j)$ with
$i + j = n$. This is a natural way to organize the entries of
row $n$: instead of a single index $k$, use the pair $(k, n-k)$.

**Why?** Sums over pairs appear naturally in:
- **Convolution products**: $\\sum_{i+j=n} a_i b_j$
- **Generating functions**: coefficient extraction
- **Double counting**: the same sum indexed two ways

You will learn:
1. `Finset.antidiagonal n` — the set of pairs summing to $n$
2. `Finset.mem_antidiagonal` — the membership characterization
3. `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk` — reindexing
4. `Finset.Nat.sum_antidiagonal_swap` — coordinate symmetry
5. `Nat.add_choose_eq` — the Vandermonde identity (convolution)

These tools let you move freely between pair-indexed and
single-indexed sums, and compute convolution products.

**Prerequisites**: `Nat.choose` identities from BinomialCoefficients,
`Nat.sum_range_choose` and `sum_congr` from BinomialTheorem,
`Finset.sum_add_distrib` from BigOpAlgebra.
"
