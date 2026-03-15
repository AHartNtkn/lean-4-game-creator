import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 1

Title "Fresh Pascal application"

Introduction
"
# Combinatorial Identity Transfer: Problem Set

Welcome to the problem set for the Binomial Theorem world. Here you
will retrieve Pascal's rule, symmetry, the row sum, and the binomial
theorem on **fresh surface forms** with **reduced scaffolding**.

No new theorems are introduced. All hints are hidden.

## Level 1: Pascal's rule on a new row

Use Pascal's rule to prove:

$$\\binom{8}{3} = \\binom{7}{2} + \\binom{7}{3}$$

This is the same recursion you used in the BinomialCoefficients world,
but on a larger row of Pascal's triangle that you have not seen before.

Recall that `Nat.choose_succ_succ` states:

$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$
"

/-- Pascal's rule: C(8, 3) = C(7, 2) + C(7, 3). -/
Statement : Nat.choose 8 3 = Nat.choose 7 2 + Nat.choose 7 3 := by
  Hint (hidden := true) "Use `rw [Nat.choose_succ_succ]`. Lean will match
  `Nat.choose 8 3` as `Nat.choose (7 + 1) (2 + 1)` and apply Pascal's
  rule."
  rw [Nat.choose_succ_succ]

Conclusion
"
You applied Pascal's rule to decompose row 8:

$$\\binom{8}{3} = \\binom{7}{2} + \\binom{7}{3} = 21 + 35 = 56$$

## Transfer moment

On paper: *\"By Pascal's rule, $\\binom{8}{3} = \\binom{7}{2} + \\binom{7}{3}$.\"*

This is the simplest possible application — a one-line rewrite.

**Retrieval check**: Pascal's rule (M28) on a fresh numerical instance.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
