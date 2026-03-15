import GameServer.Commands
import Mathlib

World "Factorials"
Level 1

Title "What is n! ?"

Introduction
"
# Factorials

Welcome to the **Factorials** world! The factorial function is one of
the most fundamental objects in discrete mathematics. It counts the
number of ways to arrange $n$ objects in a line, and it appears in
binomial coefficients, Taylor series, and throughout combinatorics.

## Definition

The factorial of a natural number $n$, written $n!$, is defined
recursively:

$$0! = 1, \\qquad (n+1)! = (n+1) \\cdot n!$$

So $5! = 5 \\cdot 4 \\cdot 3 \\cdot 2 \\cdot 1 = 120$.

## In Lean

Lean defines `Nat.factorial` recursively. The key lemmas are:

```
Nat.factorial_zero : Nat.factorial 0 = 1
Nat.factorial_succ (n : ℕ) : (n + 1).factorial = (n + 1) * n.factorial
```

There is also notation: you can write `n !` (with a space) or
`Nat.factorial n`.

## Your task

Compute $5! = 120$ by repeatedly unfolding the recursion. Use
`Nat.factorial_succ` to peel off each factor, then use
`Nat.factorial_zero` for the base case.
"

/-- Compute 5! = 120 by unfolding the recursive definition. -/
Statement : Nat.factorial 5 = 120 := by
  Hint "Apply `Nat.factorial_succ` repeatedly to unfold the recursion.
  Each application peels off one factor:

  `5! = 5 * 4!`, then `4! = 4 * 3!`, and so on.

  Try `rw [Nat.factorial_succ]` — Lean will match `5` as `4 + 1`
  and rewrite `(4 + 1).factorial` to `(4 + 1) * 4.factorial`."
  Hint (hidden := true) "Apply `rw [Nat.factorial_succ]` five times,
  then `rw [Nat.factorial_zero]`."
  rw [Nat.factorial_succ]
  Hint "Good! Now `4.factorial` appears. Apply `Nat.factorial_succ` again
  to unfold it."
  rw [Nat.factorial_succ]
  Hint "Keep going — apply `Nat.factorial_succ` three more times."
  rw [Nat.factorial_succ]
  rw [Nat.factorial_succ]
  rw [Nat.factorial_succ]
  Hint "Now the goal contains `Nat.factorial 0`. Use
  `rw [Nat.factorial_zero]` to replace it with `1`."
  Hint (hidden := true) "Try `rw [Nat.factorial_zero]`."
  rw [Nat.factorial_zero]

Conclusion
"
You computed $5! = 120$ by unfolding the recursive definition step by step:

$$5! = 5 \\cdot 4! = 5 \\cdot 4 \\cdot 3! = \\cdots = 5 \\cdot 4 \\cdot 3 \\cdot 2 \\cdot 1 \\cdot 1 = 120$$

The two key lemmas are:
- `Nat.factorial_succ`: $(n+1)! = (n+1) \\cdot n!$
- `Nat.factorial_zero`: $0! = 1$

Together, they give you the complete recursive unfolding of any
specific factorial.

## What comes next

Now that you can compute specific factorials, the next level
explores the recursion `Nat.factorial_succ` as an algebraic tool.
"

/-- `Nat.factorial_zero` states that `Nat.factorial 0 = 1`.

The factorial of zero is one, by convention and by the empty-product
principle. -/
TheoremDoc Nat.factorial_zero as "Nat.factorial_zero" in "Nat"

/-- `Nat.factorial_succ` states that
`(n + 1).factorial = (n + 1) * n.factorial`.

This is the recursive step of the factorial definition: to compute
$(n+1)!$, multiply $n!$ by $(n+1)$. -/
TheoremDoc Nat.factorial_succ as "Nat.factorial_succ" in "Nat"

/-- `Nat.factorial` is the factorial function on natural numbers.

`Nat.factorial n` computes $n! = n \cdot (n-1) \cdots 2 \cdot 1$,
with the convention that $0! = 1$. -/
DefinitionDoc Nat.factorial as "Nat.factorial"

NewTheorem Nat.factorial_zero Nat.factorial_succ
NewDefinition Nat.factorial
DisabledTactic trivial decide native_decide simp aesop simp_all
