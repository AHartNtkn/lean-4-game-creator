import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 5

Title "Pascal's rule in action"

Introduction
"
# Pascal's Rule in Action

In L01, you computed $\\binom{5}{2} = 10$ by fully unfolding the
recursion. That was systematic but tedious. Now let us use Pascal's
rule more strategically.

## The identity

Prove that $\\binom{6}{2} = \\binom{5}{1} + \\binom{5}{2}$.

This is Pascal's rule with $n = 5$, $k = 1$:

$$\\binom{6}{2} = \\binom{5}{1} + \\binom{5}{2}$$

## Strategy

A single application of `Nat.choose_succ_succ` does it. But notice
the insight: instead of computing $\\binom{6}{2} = 15$ by unfolding
*everything*, Pascal's rule lets you express it in terms of
already-known values: $\\binom{5}{1} = 5$ and $\\binom{5}{2} = 10$.

This is exactly how you compute entries in Pascal's triangle by hand:
each entry is the sum of the two entries directly above it.
"

/-- C(6,2) = C(5,1) + C(5,2) by Pascal's rule. -/
Statement : Nat.choose 6 2 = Nat.choose 5 1 + Nat.choose 5 2 := by
  Hint "Apply Pascal's rule directly. Note that `6 = 5 + 1` and `2 = 1 + 1`,
  so `Nat.choose_succ_succ` rewrites the left side to the right side.

  Try `rw [Nat.choose_succ_succ]`."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]

Conclusion
"
One rewrite does it: Pascal's rule directly gives

$$\\binom{6}{2} = \\binom{5}{1} + \\binom{5}{2} = 5 + 10 = 15$$

## Pascal's triangle

This computation reflects the structure of Pascal's triangle:

```
Row 0:                 1
Row 1:               1   1
Row 2:             1   2   1
Row 3:           1   3   3   1
Row 4:         1   4   6   4   1
Row 5:       1   5  10  10   5   1
Row 6:     1   6  15  20  15   6   1
```

Each entry is the sum of the two entries above it — that is Pascal's rule.

$\\binom{6}{2} = 15$ sits below $\\binom{5}{1} = 5$ and $\\binom{5}{2} = 10$.

## What comes next

Next, you will prove the *symmetry* of binomial coefficients:
$\\binom{n}{k} = \\binom{n}{n-k}$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
