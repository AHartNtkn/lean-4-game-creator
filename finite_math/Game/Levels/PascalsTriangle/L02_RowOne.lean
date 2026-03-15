import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 2

Title "Row 1: [1, 1]"

Introduction
"
# Row 1: [1, 1]

Row 1 of Pascal's triangle has two entries: $\\binom{1}{0}$ and $\\binom{1}{1}$.

We already know $\\binom{1}{0} = 1$ from `Nat.choose_zero_right`.
But what about $\\binom{1}{1}$?

## Pascal's rule in action

Let us verify $\\binom{1}{1} = 1$ by unfolding the recursion.

Pascal's rule with $n = 0$, $k = 0$ gives:

$$\\binom{1}{1} = \\binom{0}{0} + \\binom{0}{1} = 1 + 0 = 1$$

This is the first time we see Pascal's rule *produce a value*: the
entry $\\binom{1}{1}$ in Row 1 is the sum of $\\binom{0}{0}$ and
$\\binom{0}{1}$ from Row 0 (with $\\binom{0}{1} = 0$ since it is
beyond the end of Row 0).

## Your task

Prove that $\\binom{1}{1} = 1$ by unfolding through Pascal's rule
and the boundary conditions.
"

/-- C(1, 1) = 1, verified via Pascal's rule. -/
Statement : Nat.choose 1 1 = 1 := by
  Hint "Start by applying Pascal's rule: `Nat.choose_succ_succ` rewrites
  `Nat.choose 1 1` as `Nat.choose 0 0 + Nat.choose 0 1`.

  Since `1 = 0 + 1`, Lean matches the pattern automatically.

  Try `rw [Nat.choose_succ_succ]`."
  Hint (hidden := true) "Try `rw [Nat.choose_succ_succ]`."
  rw [Nat.choose_succ_succ]
  Hint "Good! The goal is now `Nat.choose 0 0 + Nat.choose 0 1 = 1`.

  The first term is `Nat.choose 0 0 = 1` by `Nat.choose_zero_right`.

  Try `rw [Nat.choose_zero_right]`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  rw [Nat.choose_zero_right]
  Hint "Now the goal is `1 + Nat.choose 0 1 = 1`.

  The remaining term is `Nat.choose 0 1`. Since `1 = 0 + 1`, this is
  `Nat.choose 0 (0 + 1)`, which equals 0 by `Nat.choose_zero_succ`.

  Try `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`."
  Hint (hidden := true) "Try `rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]`."
  rw [show (1 : ℕ) = 0 + 1 from rfl, Nat.choose_zero_succ]

Conclusion
"
Row 1 is confirmed: **[1, 1]**.

## The computation traced

$$\\binom{1}{1} = \\binom{0}{0} + \\binom{0}{1} = 1 + 0 = 1$$

This is Pascal's rule in its simplest form:
- `Nat.choose_succ_succ` split $\\binom{1}{1}$ into $\\binom{0}{0} + \\binom{0}{1}$
- `Nat.choose_zero_right` gave $\\binom{0}{0} = 1$
- `Nat.choose_zero_succ` gave $\\binom{0}{1} = 0$

## The triangle so far

```
Row 0:    1
Row 1:   1  1
```

Each entry in Row 1 sits below two entries in Row 0 (with implicit
zeros for entries beyond the row).

## What comes next

Row 2: **[1, 2, 1]** — where we see the first non-trivial value
emerge from the recursion.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
