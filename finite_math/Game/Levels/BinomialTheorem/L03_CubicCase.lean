import Game.Metadata

World "BinomialTheorem"
Level 3

Title "The Cubic Case"

Introduction "
# The Cubic Case: $(x + y)^3$

The quadratic case showed coefficients $1, 2, 1$. What about
$(x + y)^3$?

$$(x + y)^3 = x^3 + 3x^2y + 3xy^2 + y^3$$

The coefficients are $1, 3, 3, 1$ — row 3 of Pascal's triangle.
With two data points, a pattern emerges: the coefficient of
$x^m y^{n-m}$ in the expansion of $(x + y)^n$ is $\\binom{n}{m}$.

| $m$ | $x^m$ | $y^{3-m}$ | $\\binom{3}{m}$ | Term |
|---|---|---|---|---|
| 0 | $x^0 = 1$ | $y^3$ | $\\binom{3}{0} = 1$ | $y^3$ |
| 1 | $x$ | $y^2$ | $\\binom{3}{1} = 3$ | $3xy^2$ |
| 2 | $x^2$ | $y$ | $\\binom{3}{2} = 3$ | $3x^2y$ |
| 3 | $x^3$ | $y^0 = 1$ | $\\binom{3}{3} = 1$ | $x^3$ |

**Your task**: Verify this cubic expansion. As in the previous
level, `ring` handles the polynomial arithmetic.
"

/-- The binomial theorem for n = 3: the cubic expansion. -/
Statement (x y : ℕ) :
    (x + y) ^ 3 = x ^ 3 + 3 * x ^ 2 * y + 3 * x * y ^ 2 + y ^ 3 := by
  Hint "This is a polynomial identity over natural numbers. The `ring`
  tactic can verify it by expanding and comparing coefficients.
  Try `ring`."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
One step: `ring`.

**Two data points**: The quadratic case gave coefficients $1, 2, 1$.
The cubic case gives $1, 3, 3, 1$. Both match the corresponding rows
of Pascal's triangle. This is not a coincidence — the binomial theorem
guarantees it for every $n$.

**Why the cubic matters**: One expansion could be a coincidence. Two
expansions reveal a pattern. The rest of this world will show you how
to *derive* counting identities from this pattern by specializing
the general formula to specific values of $x$ and $y$.

Starting next level, `ring` will be disabled so you learn to carry
out the simplification steps manually using `rw`.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto
DisabledTheorem Nat.sum_range_choose
