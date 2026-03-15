import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 5

Title "Row sum identity"

Introduction
"
# Row Sum Identity: $\\sum \\binom{n}{k} = 2^n$

Now prove the row sum identity as a standalone result. You saw
this in the BinomialCoefficients world using `Nat.sum_range_choose`,
but now you know *why* it holds — it is the binomial theorem with
$x = 1, y = 1$.

## Your task

Prove $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$ using the library lemma
`Nat.sum_range_choose`.
"

/-- The row sum identity: ∑ C(n, k) = 2^n. -/
Statement (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), Nat.choose n k = 2 ^ n := by
  Hint "The library lemma `Nat.sum_range_choose` states exactly this identity.

  Try `exact Nat.sum_range_choose n`."
  Hint (hidden := true) "Try `exact Nat.sum_range_choose n`."
  exact Nat.sum_range_choose n

Conclusion
"
## Two proofs of the same identity

You now have two perspectives on why $\\sum \\binom{n}{k} = 2^n$:

**Algebraic proof** (this world, L04):
Set $x = 1, y = 1$ in the binomial theorem.

**Combinatorial proof** (BinomialCoefficients world):
Count all subsets of an $n$-element set by size.

## Transfer

On paper: *\"Setting $x = y = 1$ in the binomial theorem gives
$2^n = \\sum_{k=0}^{n} \\binom{n}{k}$.\"*

Both proofs lead to the same identity, but illuminate it differently.
The algebraic proof generalizes: different substitutions yield
different identities.

## What comes next

The next level introduces the **Vandermonde convolution**, an
identity relating binomial coefficients of different rows.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
