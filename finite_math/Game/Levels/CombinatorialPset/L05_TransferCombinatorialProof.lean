import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 5

Title "Transfer: combinatorial vs algebraic proof"

Introduction
"
# Transfer: Two proofs of the row sum identity

You know that $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$. There are (at least)
two ways to prove this:

**Algebraic proof**: Set $x = y = 1$ in the binomial theorem.
$(1 + 1)^n = \\sum \\binom{n}{k} \\cdot 1^k \\cdot 1^{n-k} = \\sum \\binom{n}{k}$.
Since $(1+1)^n = 2^n$, done.

**Combinatorial proof**: A set of $n$ elements has $2^n$ subsets.
Partitioning by size: there are $\\binom{n}{k}$ subsets of size $k$.
So $\\sum_{k=0}^{n} \\binom{n}{k} = 2^n$.

Both proofs are beautiful. The algebraic one generalizes (different
substitutions yield different identities). The combinatorial one gives
a *reason* (each coefficient counts subsets of a fixed size).

## Your task

Prove the row sum identity once more, for a specific value $n = 6$.
The focus is not the Lean proof (which is a one-liner), but the
transfer reflection in the conclusion.
"

/-- Row sum identity for n = 6: ∑ C(6, k) = 2^6 = 64. -/
Statement : ∑ k ∈ Finset.range 7, Nat.choose 6 k = 64 := by
  Hint (hidden := true) "Use `have h := Nat.sum_range_choose 6`, then `exact h`."
  have h := Nat.sum_range_choose 6
  exact h

Conclusion
"
You proved $\\sum_{k=0}^{6} \\binom{6}{k} = 64 = 2^6$.

## The two proofs side by side

**Algebraic** (binomial theorem):

> *Set $x = y = 1$:*
> *$(1 + 1)^6 = \\sum_{k=0}^{6} \\binom{6}{k} = 2^6 = 64$. $\\square$*

**Combinatorial** (subset counting):

> *A 6-element set has $2^6 = 64$ subsets. Partitioning by size:*
> *$\\binom{6}{0} + \\binom{6}{1} + \\cdots + \\binom{6}{6}$*
> *$= 1 + 6 + 15 + 20 + 15 + 6 + 1 = 64$. $\\square$*

## Why have both?

The algebraic proof generalizes: changing the substitution gives
different identities ($\\sum (-1)^k \\binom{n}{k} = 0$, etc.). The
combinatorial proof gives *meaning*: each $\\binom{n}{k}$ counts
something concrete, and the sum counts all subsets.

A working mathematician carries both perspectives. The ability to
switch between them — recognizing when a combinatorial argument is
more illuminating, or when an algebraic manipulation is more efficient
— is what this problem set exercises.

**Transfer check**: Combinatorial vs algebraic reasoning (T7) applied
to the row sum identity.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
