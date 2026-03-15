import GameServer.Commands
import Mathlib

World "Factorials"
Level 2

Title "Factorial recursion"

Introduction
"
# Using factorial_succ algebraically

In the previous level you used `Nat.factorial_succ` to compute
a specific factorial. Now you will use it as an algebraic identity.

## The task

Prove that $n! \\cdot (n + 1) = (n + 1)!$ for all $n$.

This is `Nat.factorial_succ` read in reverse: instead of unfolding
$(n+1)!$, you are *building* it from $n!$.

## Strategy

1. Rewrite the right-hand side using `Nat.factorial_succ` to get
   $(n+1) \\cdot n!$.
2. Use `mul_comm` to match the left-hand side.

You already know `mul_comm` from earlier worlds — it swaps the
order of multiplication: $a \\cdot b = b \\cdot a$.
"

/-- The factorial recursion read backward: n! * (n+1) = (n+1)!. -/
Statement (n : ℕ) : Nat.factorial n * (n + 1) = Nat.factorial (n + 1) := by
  Hint "Start by rewriting the right-hand side. Use
  `rw [Nat.factorial_succ]` to replace `(n + 1).factorial` with
  `(n + 1) * n.factorial`."
  Hint (hidden := true) "Try `rw [Nat.factorial_succ]`."
  rw [Nat.factorial_succ]
  Hint "The goal is now `n.factorial * (n + 1) = (n + 1) * n.factorial`.
  These differ only in the order of multiplication. Use `mul_comm` to
  close it."
  Hint (hidden := true) "Try `rw [mul_comm]`."
  rw [mul_comm]

Conclusion
"
You proved $n! \\cdot (n+1) = (n+1)!$ — the factorial recursion
read as a building-up identity rather than a breaking-down identity.

## Two directions of factorial_succ

- **Breaking down**: $5! = 5 \\cdot 4!$ (used in L01 for computation)
- **Building up**: $4! \\cdot 5 = 5!$ (used here for algebraic reasoning)

Both directions use the same lemma `Nat.factorial_succ`; the only
difference is whether you read it left-to-right or right-to-left.

## What comes next

The next level connects factorials to big products — specifically,
$n! = \\prod_{i=0}^{n-1}(i+1)$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
