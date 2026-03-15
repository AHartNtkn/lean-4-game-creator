import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 1

Title "Row 0: [1]"

Introduction
"
# Pascal's Triangle, Row by Row

Welcome to **Pascal's triangle**! In the Binomial Coefficients world,
you learned the recursive definition of $\\binom{n}{k}$ and the key
lemmas. Now we will build Pascal's triangle *row by row*, computing
each entry and seeing how the patterns emerge from the recursion.

## Pascal's triangle

```
Row 0:                 1
Row 1:               1   1
Row 2:             1   2   1
Row 3:           1   3   3   1
Row 4:         1   4   6   4   1
```

Each row $n$ contains the values $\\binom{n}{0}, \\binom{n}{1}, \\ldots, \\binom{n}{n}$.

## Row 0

Row 0 of Pascal's triangle consists of a single entry: $\\binom{0}{0}$.

Since choosing 0 elements from 0 elements can be done in exactly one
way (take the empty set), we have $\\binom{0}{0} = 1$.

The row is simply: **[1]**.

## Your task

Prove that $\\binom{0}{0} = 1$.
"

/-- Row 0 of Pascal's triangle: C(0, 0) = 1. -/
Statement : Nat.choose 0 0 = 1 := by
  Hint "The boundary lemma `Nat.choose_zero_right` says
  `Nat.choose n 0 = 1` for all `n`. With `n = 0`, this gives exactly
  what we need.

  Try `rw [Nat.choose_zero_right]`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]

Conclusion
"
Row 0 is confirmed: **[1]**.

This is the apex of Pascal's triangle — the single entry from which
all other rows are built by Pascal's rule.

You could also have used `Nat.choose_self` here, since $\\binom{0}{0}$
is also an instance of $\\binom{n}{n} = 1$. Both boundary lemmas agree
at $n = 0$.

## What comes next

Next, we verify Row 1: **[1, 1]**, using Pascal's rule to see the
recursion in action.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
