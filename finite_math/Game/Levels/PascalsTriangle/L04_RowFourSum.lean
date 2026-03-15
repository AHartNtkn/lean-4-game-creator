import GameServer.Commands
import Mathlib

World "PascalsTriangle"
Level 4

Title "Row 4: sum = 16"

Introduction
"
# Row 4: [1, 4, 6, 4, 1]

Row 4 of Pascal's triangle is:

$$\\binom{4}{0}, \\binom{4}{1}, \\binom{4}{2}, \\binom{4}{3}, \\binom{4}{4}
= 1, 4, 6, 4, 1$$

## Row sum identity

In the Binomial Coefficients world, you learned the row sum identity:

$$\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$$

For Row 4, this gives:

$$1 + 4 + 6 + 4 + 1 = 16 = 2^4$$

## Your task

Verify this concretely: prove that the sum of all entries in Row 4
equals 16. The mathlib lemma `Nat.sum_range_choose` gives the
general identity, which specializes to this case.

Note that `Finset.range 5 = \\{0, 1, 2, 3, 4\\}`, which indexes the
five entries of Row 4.
"

/-- The sum of Row 4 of Pascal's triangle equals 16. -/
Statement : ∑ m ∈ Finset.range 5, Nat.choose 4 m = 16 := by
  Hint "The general identity `Nat.sum_range_choose n` says:

  `∑ m ∈ Finset.range (n + 1), Nat.choose n m = 2 ^ n`

  For `n = 4`, `Nat.sum_range_choose 4` proves
  `∑ m ∈ Finset.range 5, Nat.choose 4 m = 2 ^ 4`.

  But our goal has `16` instead of `2 ^ 4`. Since `2 ^ 4 = 16`,
  `norm_num` can convert between them.

  Try `rw [Nat.sum_range_choose]` first."
  Hint (hidden := true) "Try `rw [Nat.sum_range_choose]` and then
  `norm_num` to evaluate `2 ^ 4 = 16`."
  rw [Nat.sum_range_choose]
  Hint "Good! The goal is now `2 ^ 4 = 16`. This is just arithmetic.

  Try `norm_num`."
  Hint (hidden := true) "Try `norm_num`."
  norm_num

Conclusion
"
You verified the row sum for Row 4:

$$\\binom{4}{0} + \\binom{4}{1} + \\binom{4}{2} + \\binom{4}{3} + \\binom{4}{4}
= 1 + 4 + 6 + 4 + 1 = 16 = 2^4$$

## Why the row sum is $2^n$

Every subset of a 4-element set either has 0, 1, 2, 3, or 4 elements.
The total number of subsets is $2^4 = 16$ (each element is independently
in or out). Partitioning by size:

| Size $k$ | Count $\\binom{4}{k}$ | Subsets of $\\{a,b,c,d\\}$ |
|-----------|----------------------|--------------------------|
| 0 | 1 | $\\emptyset$ |
| 1 | 4 | $\\{a\\}, \\{b\\}, \\{c\\}, \\{d\\}$ |
| 2 | 6 | $\\{a,b\\}, \\{a,c\\}, \\{a,d\\}, \\{b,c\\}, \\{b,d\\}, \\{c,d\\}$ |
| 3 | 4 | $\\{a,b,c\\}, \\{a,b,d\\}, \\{a,c,d\\}, \\{b,c,d\\}$ |
| 4 | 1 | $\\{a,b,c,d\\}$ |

Total: $1 + 4 + 6 + 4 + 1 = 16$. ✓

## What comes next

Look at Row 4 again: $1, 4, 6, 4, 1$. It reads the same forwards
and backwards. This is the **symmetry** of binomial coefficients —
the next level will verify it concretely.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
