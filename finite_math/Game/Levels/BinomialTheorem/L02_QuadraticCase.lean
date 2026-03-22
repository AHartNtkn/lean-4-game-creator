import Game.Metadata

World "BinomialTheorem"
Level 2

Title "The Quadratic Case"

Introduction "
# The Familiar Face: $(x + y)^2$

Every algebra student knows:

$$(x + y)^2 = x^2 + 2xy + y^2$$

This is the binomial theorem for $n = 2$. Let us see why by
expanding the sum from Level 1 with $n = 2$. The sum has three
terms ($m = 0, 1, 2$):

| $m$ | $x^m$ | $y^{2-m}$ | $\\binom{2}{m}$ | Term |
|---|---|---|---|---|
| 0 | $x^0 = 1$ | $y^2$ | $\\binom{2}{0} = 1$ | $y^2$ |
| 1 | $x^1 = x$ | $y^1 = y$ | $\\binom{2}{1} = 2$ | $2xy$ |
| 2 | $x^2$ | $y^0 = 1$ | $\\binom{2}{2} = 1$ | $x^2$ |

Adding them up: $y^2 + 2xy + x^2 = x^2 + 2xy + y^2$.

The abstract sum formula gives back the quadratic expansion you
already know!

**Your task**: Verify this identity. Lean's `ring` tactic handles
polynomial identities automatically — use it here.
"

/-- The binomial theorem for n = 2: the quadratic expansion. -/
Statement (x y : ℕ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  Hint "This is a polynomial identity. The `ring` tactic can verify
  it automatically by expanding both sides and checking that the
  coefficients match. Try `ring`."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion "
One step: `ring`.

The `ring` tactic proves equalities in commutative (semi)rings by
expanding both sides and checking that the coefficients match.
It can verify any polynomial identity.

**What just happened**: The binomial theorem for $n = 2$ says:

$$(x + y)^2 = \\sum_{m=0}^{2} x^m \\cdot y^{2-m} \\cdot \\binom{2}{m}$$

Each summand simplifies: $x^0$ and $y^0$ become $1$, and
$\\binom{2}{1} = 2$ produces the middle coefficient. The abstract
sum formula gives back $x^2 + 2xy + y^2$.

**Why this matters**: The rest of this world teaches you to *derive*
identities from the binomial theorem by plugging in specific values
and simplifying. This level shows that even the most familiar
algebraic identity is a special case of the sum formula. The
machinery is not just abstract notation — it is what makes every
expansion you have ever computed work.

Can we see the same pattern with a higher power? The next level
shows you the cubic case.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto
DisabledTheorem Nat.sum_range_choose
