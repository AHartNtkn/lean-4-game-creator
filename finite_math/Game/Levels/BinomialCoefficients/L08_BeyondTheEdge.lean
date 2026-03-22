import Game.Metadata

World "BinomialCoefficients"
Level 8

Title "Beyond the Edge"

Introduction "
# When $k > n$: Zero Choices

What happens when you try to choose more items than you have?

There are **zero** ways to do this:

$$k > n \\implies \\binom{n}{k} = 0$$

This may feel obvious, but it's worth noting explicitly because
`Nat.choose` is a **total function** — it accepts any pair of
natural numbers, even when $k > n$. The result is always $0$
in that case.

In Lean:
```
Nat.choose_eq_zero_of_lt : n < k → Nat.choose n k = 0
```

Note the argument order: the hypothesis is `n < k` (not `k > n`),
and the conclusion is `Nat.choose n k = 0`.

**Proof patterns for theorems with hypotheses**: You've now seen
two styles for providing inequality proofs:
- `apply f` then `omega` (Level 5) — let `apply` decompose the goal
- `have h : P := by omega` then `rw [f h]` (Level 6) — name the proof

There's a third, more concise style: `exact f (by omega)`. This
provides the proof **inline** as an argument. All three are equivalent.

**Your task**: Prove $\\binom{3}{5} = 0$.
"

/-- `Nat.choose_eq_zero_of_lt` states that `Nat.choose n k = 0`
when `n < k`.

## Syntax
```
apply Nat.choose_eq_zero_of_lt
omega
```
or equivalently:
```
exact Nat.choose_eq_zero_of_lt (by omega)
```

## When to use it
When you see `Nat.choose n k` where `k > n` and need to simplify to `0`.

## Warning
The hypothesis is `n < k`, NOT `k > n`. Both mean the same thing,
but the order matters for pattern matching.
-/
TheoremDoc Nat.choose_eq_zero_of_lt as "Nat.choose_eq_zero_of_lt" in "Choose"

/-- C(3, 5) = 0: you cannot choose 5 items from 3. -/
Statement : Nat.choose 3 5 = 0 := by
  Hint "You cannot choose 5 items from only 3.
  Use `apply Nat.choose_eq_zero_of_lt` to apply the theorem,
  then prove the inequality `3 < 5`."
  Hint (hidden := true) "Try `apply Nat.choose_eq_zero_of_lt`."
  apply Nat.choose_eq_zero_of_lt
  Hint "The goal is `3 < 5`. Use `omega` to close it."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
$\\binom{3}{5} = 0$ — there are no 5-element subsets of a 3-element set.

The **domain picture** of `Nat.choose`:
- $0 \\le k \\le n$: interesting values, forming Pascal's triangle
- $k = 0$ or $k = n$: boundary value $1$
- $k > n$: always $0$

This means Pascal's triangle has a triangular shape: row $n$ has
nonzero entries only in positions $0, 1, \\ldots, n$.

The converse is also true for $k \\ge 1$: if $\\binom{n}{k} = 0$ and
$k \\ge 1$, then $k > n$. So $\\binom{n}{k} = 0$ if and only if $k > n$
(for positive $k$).

This convention — $\\binom{n}{k} = 0$ outside the triangle — is a
deliberate **design choice**, not a mathematical accident. It makes
formulas cleaner: Pascal's identity
$\\binom{n+1}{k+1} = \\binom{n}{k} + \\binom{n}{k+1}$ works without
any boundary conditions because the out-of-range terms are simply $0$.
This is the same principle behind $0! = 1$ and $x^0 = 1$: defining
edge cases to be the identity element of the operation eliminates
special cases from the formulas.

**Pattern**: Use `apply Nat.choose_eq_zero_of_lt` then `omega`.
Or equivalently: `exact Nat.choose_eq_zero_of_lt (by omega)`.
This is the **collect-and-close** pattern (named in FinsetInduction):
state a key structural fact (here via `apply`), then close the
arithmetic obligation with `omega`. You'll see this pattern repeatedly.
"

NewTheorem Nat.choose_eq_zero_of_lt

TheoremTab "Choose"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl fin_cases interval_cases by_cases tauto linarith nlinarith
DisabledTheorem Nat.choose_symm_add Nat.choose_symm_of_eq_add Nat.choose_succ_self_right Nat.choose_eq_one_iff
