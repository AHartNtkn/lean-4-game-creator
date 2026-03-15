import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 2

Title "Boundary values"

Introduction
"
# Boundary values of $\\binom{n}{k}$

The binomial coefficient $\\binom{n}{k}$ has several important
boundary identities. You already know two from L01:

- `Nat.choose_zero_right`: $\\binom{n}{0} = 1$
- `Nat.choose_zero_succ`: $\\binom{0}{k+1} = 0$

There is a third boundary identity:

```
Nat.choose_self (n : ℕ) : Nat.choose n n = 1
```

This says: choosing *all* $n$ elements from a set of $n$ can be done
in exactly one way — take the whole set.

## Your task

Prove this chain of equalities:

$$\\binom{4}{0} + \\binom{4}{4} + \\binom{0}{3} = 2$$

The left-hand side is $1 + 1 + 0 = 2$.

Use the three boundary lemmas to simplify each term.
"

/-- The three boundary values of choose in one equation. -/
Statement : Nat.choose 4 0 + Nat.choose 4 4 + Nat.choose 0 3 = 2 := by
  Hint "Rewrite each term using the appropriate boundary lemma:
  - `Nat.choose_zero_right` for the first term ($k = 0$)
  - `Nat.choose_self` for the second term ($k = n$)
  - `Nat.choose_zero_succ` for the third term ($n = 0, k > 0$)

  Try `rw [Nat.choose_zero_right]` to start."
  Hint (hidden := true) "Try
  `rw [Nat.choose_zero_right, Nat.choose_self, Nat.choose_zero_succ]`."
  rw [Nat.choose_zero_right]
  Hint "Good! Now the first term is `1`. Simplify `Nat.choose 4 4` using
  `Nat.choose_self`."
  rw [Nat.choose_self]
  Hint "Finally, simplify `Nat.choose 0 3`. Note that `3 = 2 + 1`, so
  `Nat.choose_zero_succ` applies."
  Hint (hidden := true) "Try `rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_zero_succ]`
  or use `Nat.choose_eq_zero_of_lt` instead."
  rw [show (3 : ℕ) = 2 + 1 from rfl, Nat.choose_zero_succ]

Conclusion
"
You verified that $\\binom{4}{0} + \\binom{4}{4} + \\binom{0}{3} = 1 + 1 + 0 = 2$.

## The three boundary lemmas

| Lemma | Statement | Intuition |
|-------|-----------|-----------|
| `choose_zero_right` | $\\binom{n}{0} = 1$ | One way to choose nothing |
| `choose_self` | $\\binom{n}{n} = 1$ | One way to choose everything |
| `choose_zero_succ` | $\\binom{0}{k+1} = 0$ | Cannot choose from nothing |

These are the base cases of the recursion. Together with Pascal's
rule (`choose_succ_succ`), they completely determine all values of
$\\binom{n}{k}$.

## What comes next

What happens when $k > n$? The answer is zero, but the proof
requires a different lemma.
"

/-- `Nat.choose_self` states that `Nat.choose n n = 1`.

There is exactly one way to choose all `n` elements from a set
of `n` elements: take the entire set. -/
TheoremDoc Nat.choose_self as "Nat.choose_self" in "Nat"

NewTheorem Nat.choose_self
DisabledTactic trivial decide native_decide simp aesop simp_all
