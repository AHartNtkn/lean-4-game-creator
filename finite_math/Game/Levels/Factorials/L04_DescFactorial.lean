import GameServer.Commands
import Mathlib

World "Factorials"
Level 4

Title "Descending factorials"

Introduction
"
# Descending factorials

The **descending factorial** (also called the **falling factorial** or
**Pochhammer symbol**) is a close cousin of the ordinary factorial.
It counts the number of ways to choose $k$ objects from $n$ and
arrange them in order (i.e., the number of $k$-permutations of $n$
objects).

## Definition

$$n^{\\underline{k}} = n(n-1)(n-2)\\cdots(n-k+1)$$

This is a product of $k$ consecutive descending integers starting
from $n$. In Lean:

```
Nat.descFactorial (n : ℕ) : ℕ → ℕ
```

with two key lemmas:

```
Nat.descFactorial_zero (n : ℕ) : n.descFactorial 0 = 1
Nat.descFactorial_succ (n k : ℕ) :
  n.descFactorial (k + 1) = (n - k) * n.descFactorial k
```

## Your task

Compute $5^{\\underline{3}} = 5 \\cdot 4 \\cdot 3 = 60$.

Use `Nat.descFactorial_succ` to unfold the recursion three times,
then `Nat.descFactorial_zero` for the base case.
"

/-- Compute the descending factorial 5 * 4 * 3 = 60. -/
Statement : Nat.descFactorial 5 3 = 60 := by
  Hint "Apply `Nat.descFactorial_succ` to peel off the first factor.
  Since `3 = 2 + 1`, the lemma gives:

  `5.descFactorial 3 = (5 - 2) * 5.descFactorial 2 = 3 * 5.descFactorial 2`

  Try `rw [Nat.descFactorial_succ]`."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_succ]`."
  rw [Nat.descFactorial_succ]
  Hint "Now apply `Nat.descFactorial_succ` again to unfold
  `5.descFactorial 2`."
  rw [Nat.descFactorial_succ]
  Hint "One more application of `Nat.descFactorial_succ` to unfold
  `5.descFactorial 1`."
  rw [Nat.descFactorial_succ]
  Hint "Now the goal contains `5.descFactorial 0`. Use
  `Nat.descFactorial_zero` to replace it with `1`."
  Hint (hidden := true) "Try `rw [Nat.descFactorial_zero]`."
  rw [Nat.descFactorial_zero]

Conclusion
"
You computed $5^{\\underline{3}} = 60$ by unfolding the recursion:

$$5^{\\underline{3}} = (5-2) \\cdot 5^{\\underline{2}}
= 3 \\cdot (5-1) \\cdot 5^{\\underline{1}}
= 3 \\cdot 4 \\cdot (5-0) \\cdot 5^{\\underline{0}}
= 3 \\cdot 4 \\cdot 5 \\cdot 1 = 60$$

## Factorial vs. descending factorial

Notice the difference in the recursion:
- **Factorial**: $(n+1)! = (n+1) \\cdot n!$ — peels off from the *top*
- **Descending factorial**: $n^{\\underline{k+1}} = (n-k) \\cdot n^{\\underline{k}}$ — peels off from the *bottom*

The ordinary factorial $n!$ is the special case where you descend
all the way: $n^{\\underline{n}} = n!$. We will prove this in the
next level.

## What comes next

You will prove the key relationship: $n^{\\underline{n}} = n!$.
"

/-- `Nat.descFactorial_zero` states that `n.descFactorial 0 = 1`.

The descending factorial with zero terms is one, by the
empty-product convention. -/
TheoremDoc Nat.descFactorial_zero as "Nat.descFactorial_zero" in "Nat"

/-- `Nat.descFactorial_succ` states that
`n.descFactorial (k + 1) = (n - k) * n.descFactorial k`.

This unfolds one step of the descending factorial recursion. -/
TheoremDoc Nat.descFactorial_succ as "Nat.descFactorial_succ" in "Nat"

/-- `Nat.descFactorial n k` is the descending factorial
$n^{\underline{k}} = n(n-1)\cdots(n-k+1)$.

It counts the number of ways to choose $k$ objects from $n$ and
arrange them in order. -/
DefinitionDoc Nat.descFactorial as "Nat.descFactorial"

NewTheorem Nat.descFactorial_zero Nat.descFactorial_succ
NewDefinition Nat.descFactorial
DisabledTactic trivial decide native_decide simp aesop simp_all
