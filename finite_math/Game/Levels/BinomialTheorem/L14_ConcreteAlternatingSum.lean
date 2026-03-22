import Game.Metadata

World "BinomialTheorem"
Level 14

Title "A Concrete Alternating Sum"

Introduction "
# Checking the Alternating Sum: Row 4

Before proving the general alternating sum identity, let us verify
a specific case. Row 4 of Pascal's triangle is:

$$\\binom{4}{0},\\; \\binom{4}{1},\\; \\binom{4}{2},\\; \\binom{4}{3},\\; \\binom{4}{4} = 1,\\; 4,\\; 6,\\; 4,\\; 1$$

The alternating sum assigns alternating signs $+, -, +, -, +$:

$$1 - 4 + 6 - 4 + 1 = 0$$

This is surprising: the enormous entries $4$ and $6$ cancel perfectly
with the smaller entries. And this works for *every* row (except
row 0). The next level proves this in general.

**Your task**: Verify the numerical identity $1 - 4 + 6 - 4 + 1 = 0$
over $\\mathbb{Z}$. This is pure integer arithmetic — `omega`
handles it.
"

/-- The alternating sum of row 4 of Pascal's triangle is zero. -/
Statement : (1 : ℤ) - 4 + 6 - 4 + 1 = 0 := by
  Hint "This is a concrete arithmetic fact over the integers.
  The `omega` tactic can verify linear integer arithmetic."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
One step: `omega`.

This is the pattern you saw with `ring` in Levels 2 and 3: verify a
concrete case before proving the general result. Here, the concrete
case is $1 - 4 + 6 - 4 + 1 = 0$ — the alternating sum of row 4.

**Why over $\\mathbb{Z}$?** The alternating sum involves subtraction:
$1 - 4 = -3$. Over $\\mathbb{N}$, subtraction is truncated
($1 - 4 = 0$), so the identity would not hold. Working over
$\\mathbb{Z}$ lets the negative intermediate values exist.

**In the next level**, you will prove this for every row: the
alternating sum $\\sum_{m=0}^{n} (-1)^m \\binom{n}{m} = 0$ for all
$n \\geq 1$. The proof uses the same specialize-simplify-rewrite
pattern, now over $\\mathbb{Z}$ with $x = -1$.
"

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num tauto ring ring_nf
