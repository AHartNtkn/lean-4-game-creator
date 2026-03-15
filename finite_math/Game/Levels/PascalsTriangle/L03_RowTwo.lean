import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 3

Title "Row 2: [1, 2, 1]"

Introduction
"
# Row 2: [1, 2, 1]

Row 2 of Pascal's triangle is where the pattern first becomes
interesting. The entries are:

$$\\binom{2}{0} = 1, \\quad \\binom{2}{1} = 2, \\quad \\binom{2}{2} = 1$$

The value $\\binom{2}{1} = 2$ is the first entry greater than 1
in Pascal's triangle. It comes from Pascal's rule:

$$\\binom{2}{1} = \\binom{1}{0} + \\binom{1}{1} = 1 + 1 = 2$$

The \"2\" in the middle of Row 2 is the sum of the two \"1\"s
above it in Row 1.

## Your task

Verify the middle entry: prove that $\\binom{2}{1} = 2$.

You can use Pascal's rule to split it, then simplify the
resulting terms using boundary conditions.
"

/-- The middle entry of Row 2: C(2, 1) = 2. -/
Statement : Nat.choose 2 1 = 2 := by
  Hint "Apply Pascal's rule to split `Nat.choose 2 1` into
  `Nat.choose 1 0 + Nat.choose 1 1`.

  Try `rw [Nat.choose_succ_succ]`."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "Good! The goal is `Nat.choose 1 0 + Nat.choose 1 1 = 2`.

  Simplify `Nat.choose 1 0 = 1` with `Nat.choose_zero_right`.

  Try `rw [Nat.choose_zero_right]`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]
  Hint "The goal is `1 + Nat.choose 1 1 = 2`. Simplify
  `Nat.choose 1 1 = 1` with `Nat.choose_self`.

  Try `rw [Nat.choose_self]`."
  Hint (hidden := true) "Try `rw [Nat.choose_self]`."
  rw [Nat.choose_self]

Conclusion
"
Row 2 confirmed: **[1, 2, 1]**.

## The computation

$$\\binom{2}{1} = \\binom{1}{0} + \\binom{1}{1} = 1 + 1 = 2$$

The three lemmas used:
- `Nat.choose_succ_succ` — split by Pascal's rule
- `Nat.choose_zero_right` — $\\binom{1}{0} = 1$
- `Nat.choose_self` — $\\binom{1}{1} = 1$

## The triangle so far

```
Row 0:      1
Row 1:     1  1
Row 2:    1  2  1
```

Notice how the \"2\" in the middle of Row 2 is literally the sum of
the two entries directly above it in Row 1. This visual pattern —
each entry is the sum of the two entries above — *is* Pascal's rule.

## What comes next

We skip ahead to Row 4 to see a more complex row and verify
its row sum.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
