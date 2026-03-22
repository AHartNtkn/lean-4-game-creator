import Game.Levels.BinomialCoefficients.L01_BoundaryValues
import Game.Levels.BinomialCoefficients.L02_ChoosingOne
import Game.Levels.BinomialCoefficients.L03_PascalsIdentity
import Game.Levels.BinomialCoefficients.L04_PascalComputation
import Game.Levels.BinomialCoefficients.L05_BoundaryPractice
import Game.Levels.BinomialCoefficients.L06_Symmetry
import Game.Levels.BinomialCoefficients.L07_DerivingChooseSelf
import Game.Levels.BinomialCoefficients.L08_BeyondTheEdge
import Game.Levels.BinomialCoefficients.L09_FactorialFormula
import Game.Levels.BinomialCoefficients.L10_AbsorptionIdentity
import Game.Levels.BinomialCoefficients.L11_RetrievalPractice
import Game.Levels.BinomialCoefficients.L12_CoachingBossPattern
import Game.Levels.BinomialCoefficients.L13_SumSimplification
import Game.Levels.BinomialCoefficients.L14_GaussSum
import Game.Levels.BinomialCoefficients.L15_HockeyStick
import Game.Levels.BinomialCoefficients.L16_Boss

World "BinomialCoefficients"
Title "Binomial Coefficients"

Introduction "
# Binomial Coefficients

A committee of 2 must be chosen from 4 candidates. How many possible
committees are there? And how would you *prove* your answer is correct?

The answer is $\\binom{4}{2} = 6$, the **binomial coefficient**.
These numbers have a long history: the arrangement we now call
**Pascal's triangle** was studied by Chinese mathematician Jia Xian
around 1050 CE and by Persian mathematician Omar Khayyam around 1100 CE —
over 500 years before Blaise Pascal published his treatise in 1665.

In this world, you'll learn the Lean formalization `Nat.choose n k` and prove
identities using its key properties:

- **Boundary values**: $\\binom{n}{0} = 1$, $\\binom{n}{n} = 1$, $\\binom{n}{1} = n$
- **Pascal's identity**: $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$
- **Symmetry**: $\\binom{n}{k} = \\binom{n}{n-k}$
- **Beyond the edge**: $\\binom{n}{k} = 0$ when $k > n$
- **Factorial formula**: $\\binom{n}{k} \\cdot k! \\cdot (n-k)! = n!$
- **Absorption identity**: $(n+1) \\cdot \\binom{n}{k} = (k+1) \\cdot \\binom{n+1}{k+1}$

Pascal's identity is the **recursive heart** of the binomial coefficient.
Combined with the boundary values, it lets you compute any $\\binom{n}{k}$
by building Pascal's triangle from the top.

After learning these identities, you'll prove a cross-world connection
(the Gauss sum equals $\\binom{n+1}{2}$), the **hockey stick identity**
$\\sum_{i=0}^{n} \\binom{i}{k} = \\binom{n+1}{k+1}$, and then tackle the
boss: proving by induction that
$2 \\cdot \\binom{n+2}{2} = (n+1)(n+2)$, integrating Pascal's identity
with the peel + IH + ring pattern from the summation worlds.

**Prerequisites**: `Nat.factorial` from SummationFormulas, `induction`
from FinsetInduction, `ring` from BigOpAlgebra, `omega` from MeetFin.
"
