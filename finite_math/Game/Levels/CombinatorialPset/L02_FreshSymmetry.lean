import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 2

Title "Fresh symmetry application"

Introduction
"
# Symmetry on a new pair

Prove that $\\binom{10}{7} = \\binom{10}{3}$ using the symmetry of
binomial coefficients.

Since $7 = 10 - 3$, this is `Nat.choose_symm` with $n = 10, k = 3$.

Recall the lemma:

$$k \\le n \\implies \\binom{n}{n - k} = \\binom{n}{k}$$
"

/-- Symmetry: C(10, 7) = C(10, 3). -/
Statement : Nat.choose 10 7 = Nat.choose 10 3 := by
  Hint (hidden := true) "Rewrite `7` as `10 - 3`, then apply `Nat.choose_symm`.

  Try `rw [show (7 : ℕ) = 10 - 3 from rfl, Nat.choose_symm]`, then
  close `3 ≤ 10` with `omega`."
  rw [show (7 : ℕ) = 10 - 3 from rfl, Nat.choose_symm]
  omega

Conclusion
"
You proved $\\binom{10}{7} = \\binom{10}{3} = 120$ by symmetry.

## The pattern

To use `Nat.choose_symm` when the goal has `Nat.choose n m` with
$m > n/2$:

1. Rewrite `m` as `n - k` where $k = n - m$.
2. Apply `Nat.choose_symm`.
3. Prove $k \\le n$ (usually by `omega`).

## Transfer moment

On paper: *\"By symmetry, $\\binom{10}{7} = \\binom{10}{10-7} = \\binom{10}{3}$.\"*

Combinatorially: choosing 7 elements from 10 is the same as choosing
which 3 to leave out.

**Retrieval check**: Symmetry (M30) on a fresh pair `(10, 7)`.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
