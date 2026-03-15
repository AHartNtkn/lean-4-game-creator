import GameServer.Commands
import Mathlib

World "CombinatorialPset"
Level 6

Title "Transfer: the binomial theorem as a tool"

Introduction
"
# Transfer: The binomial theorem as an identity generator

The binomial theorem is not just one identity — it is a **factory** for
identities. Every substitution of specific values for $x$ and $y$ produces
a new equation.

## The method

Given a target identity involving $\\binom{n}{k}$, ask: *\"Is there a
substitution of $x$ and $y$ that produces this?\"*

| Substitution | Identity |
|-------------|---------|
| $x = 1, y = 1$ | $\\sum \\binom{n}{k} = 2^n$ (row sum) |
| $x = 1, y = -1$ | $\\sum (-1)^k \\binom{n}{k} = 0$ (alternating sum) |
| $x = 1, y = 2$ | $\\sum 2^{n-k} \\binom{n}{k} = 3^n$ (Level 4) |
| $x = -1, y = 2$ | $\\sum (-1)^k 2^{n-k} \\binom{n}{k} = 1$ (Boss of W19) |

## Your task

Prove the alternating sum identity for a specific $n$. This retrieves
the alternating sum lemma on a fresh surface form.
"

/-- Alternating sum for n = 5: ∑ (-1)^k * C(5, k) = 0. -/
Statement :
    ∑ m ∈ Finset.range 6, (-1 : ℤ) ^ m * ↑(Nat.choose 5 m) = 0 := by
  Hint (hidden := true) "Apply `Int.alternating_sum_range_choose_of_ne` with
  a proof that `5 ≠ 0`.

  Try `exact Int.alternating_sum_range_choose_of_ne (by omega)`."
  exact Int.alternating_sum_range_choose_of_ne (by omega)

Conclusion
"
You proved $\\sum_{k=0}^{5} (-1)^k \\binom{5}{k} = 0$.

Expanding: $1 - 5 + 10 - 10 + 5 - 1 = 0$. ✓

## Transfer: the binomial theorem on paper

On a mathematics exam, you might see:

> *\"Prove that $\\sum_{k=0}^{n} (-1)^k \\binom{n}{k} = 0$ for $n \\ge 1$.\"*

A good paper proof:

> *Set $x = 1, y = -1$ in the binomial theorem:*
> *$(1 + (-1))^n = \\sum_{k=0}^{n} 1^k (-1)^{n-k} \\binom{n}{k}$.*
> *The left side is $0^n = 0$ for $n \\ge 1$.*
> *Since $1^k = 1$, the right side simplifies to*
> *$\\sum_{k=0}^{n} (-1)^{n-k} \\binom{n}{k}$.*
> *By reindexing (or noting $(-1)^{n-k} = (-1)^n \\cdot (-1)^{-k} = (-1)^n / (-1)^k$),*
> *the identity follows. $\\square$*

The Lean proof invokes the library lemma directly. The paper proof
*explains* the lemma.

## The key insight

The binomial theorem is a **tool**, not just a theorem. When you see
an identity involving $\\binom{n}{k}$ weighted by powers, ask: *\"What
values of $x$ and $y$ produce this?\"*

**Transfer check**: Binomial theorem as tool (T7, T10) — recognizing
the substitution strategy and stating the proof in paper language.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
