import Game.Levels.BinomialTheorem.L01_MeetAddPow
import Game.Levels.BinomialTheorem.L02_QuadraticCase
import Game.Levels.BinomialTheorem.L03_CubicCase
import Game.Levels.BinomialTheorem.L04_PowersOfOne
import Game.Levels.BinomialTheorem.L05_RewritingSummands
import Game.Levels.BinomialTheorem.L06_FlippingEquations
import Game.Levels.BinomialTheorem.L07_RewritingHypotheses
import Game.Levels.BinomialTheorem.L08_RowSum
import Game.Levels.BinomialTheorem.L09_PowersetMeetsRowSum
import Game.Levels.BinomialTheorem.L10_DifferentSpecialization
import Game.Levels.BinomialTheorem.L11_DescendingPowers
import Game.Levels.BinomialTheorem.L12_WeightedRowSum
import Game.Levels.BinomialTheorem.L13_WorkingOverIntegers
import Game.Levels.BinomialTheorem.L14_ConcreteAlternatingSum
import Game.Levels.BinomialTheorem.L15_Boss

World "BinomialTheorem"
Title "Binomial Theorem"

Introduction "
# The Binomial Theorem

Why are $\\binom{n}{k}$ called **binomial** coefficients? Because they
are the coefficients when you expand a **binomial** (two-term sum)
raised to a power:

$$(x + y)^n = \\sum_{m=0}^{n} \\binom{n}{m}\\, x^m\\, y^{n-m}$$

This identity is the **binomial theorem**. It connects the algebraic
operation of raising a sum to a power with the combinatorial operation
of choosing subsets.

In the BinomialCoefficients world, you proved identities about
$\\binom{n}{k}$ using its recursive definition (Pascal's identity).
In the Powerset world, you saw that $\\binom{n}{k}$ counts the
$k$-element subsets of an $n$-element set.

Now you will see the **third face** of binomial coefficients: their
role as coefficients in polynomial expansion. By plugging in specific
values of $x$ and $y$, the binomial theorem generates counting
identities for free:

- $x = y = 1$: the **row sum** $\\sum \\binom{n}{m} = 2^n$
- $x = 2, y = 1$: the **weighted sum** $\\sum \\binom{n}{m} \\cdot 2^m = 3^n$
- $x = -1, y = 1$ (over $\\mathbb{Z}$): the **alternating sum** $\\sum (-1)^m \\binom{n}{m} = 0$

The key new proof pattern is **specialization**: start with the
general `add_pow`, plug in specific values, simplify the summand
using `one_pow` and `one_mul`, and read off the identity.

**Prerequisites**: `Finset.sum_congr` from BigOpAlgebra,
`Nat.choose` identities from BinomialCoefficients,
`card_powerset` and `card_powersetCard` from Powerset.
"
