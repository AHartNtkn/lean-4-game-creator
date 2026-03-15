import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 6

Title "Transfer: Pascal's triangle from two rules"

Introduction
"
# Transfer: Pascal's Triangle from Two Rules

You have now computed Rows 0 through 2 entry by entry, verified the
sum and symmetry of Row 4, and seen how every entry in Pascal's
triangle is determined by just two rules:

**Rule 1 (Boundary):** The edges of the triangle are always 1.
$$\\binom{n}{0} = 1 \\qquad \\text{and} \\qquad \\binom{n}{n} = 1$$

**Rule 2 (Pascal's rule):** Each interior entry is the sum of the
two entries directly above it.
$$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$$

## Transfer moment

On paper, you would describe Pascal's triangle as follows:

> *Start with a 1 at the top. Each subsequent row begins and ends
> with 1. Every other entry is the sum of the two entries directly
> above it in the previous row. Row $n$ contains $n+1$ entries,
> and the $k$-th entry (counting from 0) is $\\binom{n}{k}$.*

## Your task

As a final verification, prove both endpoint identities for Row 5:
$\\binom{5}{0} = 1$ and $\\binom{5}{5} = 1$.

This confirms that Row 5 begins and ends with 1, just as Rule 1
predicts.
"

/-- The endpoints of Row 5: C(5, 0) = 1 and C(5, 5) = 1. -/
Statement : Nat.choose 5 0 = 1 ∧ Nat.choose 5 5 = 1 := by
  Hint "Split the conjunction into two goals using `constructor`.

  Try `constructor`."
  Hint (hidden := true) "Try `constructor`."
  constructor
  Hint "**First goal**: prove `Nat.choose 5 0 = 1`.

  This is `Nat.choose_zero_right` with `n = 5`.

  Try `rw [Nat.choose_zero_right]`."
  Hint (hidden := true) "Try `rw [Nat.choose_zero_right]`."
  · rw [Nat.choose_zero_right]
  Hint "**Second goal**: prove `Nat.choose 5 5 = 1`.

  This is `Nat.choose_self` with `n = 5`.

  Try `rw [Nat.choose_self]`."
  Hint (hidden := true) "Try `rw [Nat.choose_self]`."
  · rw [Nat.choose_self]

Conclusion
"
Congratulations on completing **Pascal's Triangle, Row by Row**!

## What you verified

| Row | Entries | Verified |
|-----|---------|----------|
| 0 | [1] | $\\binom{0}{0} = 1$ ✓ |
| 1 | [1, 1] | $\\binom{1}{1} = 1$ via Pascal's rule ✓ |
| 2 | [1, 2, 1] | $\\binom{2}{1} = 2$ via Pascal's rule ✓ |
| 4 | [1, 4, 6, 4, 1] | Row sum = 16 = $2^4$ ✓ |
| 4 | symmetric | $\\binom{4}{1} = \\binom{4}{3}$ ✓ |
| 5 | endpoints | $\\binom{5}{0} = \\binom{5}{5} = 1$ ✓ |

## The two rules that build the whole triangle

Every entry in Pascal's infinite triangle is determined by:

1. **Boundary**: $\\binom{n}{0} = 1$ and $\\binom{n}{n} = 1$
2. **Recursion**: $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$

From these two rules, all the properties follow:
- The row sum $\\sum_k \\binom{n}{k} = 2^n$
- The symmetry $\\binom{n}{k} = \\binom{n}{n-k}$
- The specific values $\\binom{n}{1} = n$, $\\binom{n}{2} = \\frac{n(n-1)}{2}$, etc.

## Transfer

On paper, Pascal's triangle is drawn as:

```
         1
        1  1
       1  2  1
      1  3  3  1
     1  4  6  4  1
    1  5 10 10  5  1
```

> *Each row starts and ends with 1. Every interior entry is
> the sum of the two entries directly above it. The $k$-th
> entry of Row $n$ is $\\binom{n}{k}$, and the recursion
> $\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$ is
> precisely the \"add the two entries above\" rule.*

## What comes next

The course continues with the **binomial theorem** and more
advanced identities involving binomial coefficients.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
