import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 3

Title "A sum involving choose"

Introduction
"
# Vandermonde on fresh values

Apply Vandermonde's identity to a new triple of values.

Prove:

$$\\binom{7}{3} = \\sum_{(i,j) \\in \\text{antidiagonal}(3)} \\binom{4}{i} \\cdot \\binom{3}{j}$$

This is `Nat.add_choose_eq` with $m = 4, n = 3, k = 3$, since $7 = 4 + 3$.

The right side expands to:
$$\\binom{4}{0}\\binom{3}{3} + \\binom{4}{1}\\binom{3}{2} + \\binom{4}{2}\\binom{3}{1} + \\binom{4}{3}\\binom{3}{0}$$
$$= 1 \\cdot 1 + 4 \\cdot 3 + 6 \\cdot 3 + 4 \\cdot 1 = 1 + 12 + 18 + 4 = 35$$

And indeed $\\binom{7}{3} = 35$. ✓
"

/-- Vandermonde: C(7, 3) as a convolution of rows 4 and 3. -/
Statement : Nat.choose 7 3 =
    ∑ ij ∈ Finset.antidiagonal 3, Nat.choose 4 ij.1 * Nat.choose 3 ij.2 := by
  Hint (hidden := true) "Note that `7 = 4 + 3`. Apply `Nat.add_choose_eq`
  with `m = 4, n = 3, k = 3`.

  Try `exact Nat.add_choose_eq 4 3 3`."
  exact Nat.add_choose_eq 4 3 3

Conclusion
"
You applied Vandermonde's identity to decompose $\\binom{7}{3}$ as a
convolution of rows 4 and 3.

## The computation

| $i$ | $j = 3-i$ | $\\binom{4}{i}$ | $\\binom{3}{j}$ | Product |
|-----|-----------|-----------------|-----------------|---------|
| 0 | 3 | 1 | 1 | 1 |
| 1 | 2 | 4 | 3 | 12 |
| 2 | 1 | 6 | 3 | 18 |
| 3 | 0 | 4 | 1 | 4 |
| **Total** | | | | **35** |

## Transfer moment

On paper: *\"By Vandermonde's identity with $m = 4, n = 3$:*
*$\\binom{7}{3} = \\sum_{j=0}^{3} \\binom{4}{j} \\binom{3}{3-j} = 1 + 12 + 18 + 4 = 35$. $\\square$\"*

Combinatorially: choosing 3 people from a group of 4 men and 3 women,
by splitting over how many men are chosen.

**Retrieval check**: Vandermonde (M31) on fresh values $(4, 3, 3)$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
