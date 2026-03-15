import GameServer.Commands
import Mathlib

World "BinomialCoefficients"
Level 3

Title "Choose zero when k > n"

Introduction
"
# $\\binom{n}{k} = 0$ when $k > n$

A common misconception (C10) is that $\\binom{n}{k}$ is always
positive. In fact, when $k > n$, there are *no* ways to choose
$k$ elements from a set of $n$ — you simply do not have enough
elements. So $\\binom{n}{k} = 0$.

## The mathlib lemma

```
Nat.choose_eq_zero_of_lt {n k : ℕ} (h : n < k) : Nat.choose n k = 0
```

This takes a proof that `n < k` and returns the equation
`Nat.choose n k = 0`.

## Your task

Prove that $\\binom{3}{5} = 0$. You need to apply
`Nat.choose_eq_zero_of_lt` with a proof that `3 < 5`.
"

/-- C(3, 5) = 0 because you can't choose 5 from 3. -/
Statement : Nat.choose 3 5 = 0 := by
  Hint "Apply `Nat.choose_eq_zero_of_lt` to reduce this to proving `3 < 5`.

  Try `apply Nat.choose_eq_zero_of_lt`."
  Hint (hidden := true) "Try `apply Nat.choose_eq_zero_of_lt` first,
  then close the resulting `3 < 5` goal with `omega`."
  apply Nat.choose_eq_zero_of_lt
  Hint "The goal is now `3 < 5`. This is a concrete numerical inequality.

  Use `omega` to close it."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion
"
You proved that $\\binom{3}{5} = 0$ — you cannot choose 5 elements
from a set of only 3.

## The misconception

It is tempting to think that $\\binom{n}{k}$ is always meaningful
and positive. But the definition gives $\\binom{n}{k} = 0$ whenever
$k > n$. This is not a convention — it follows directly from the
recursive definition and the boundary condition $\\binom{0}{k+1} = 0$.

## The key lemma

`Nat.choose_eq_zero_of_lt` takes a proof of `n < k` and returns
`Nat.choose n k = 0`. The proof obligation `n < k` is a concrete
inequality that `omega` handles.

## What comes next

Now that you know the boundary behavior, the next level introduces
Pascal's rule — the central recursion that defines all values of
$\\binom{n}{k}$.
"

/-- `Nat.choose_eq_zero_of_lt` states that `n < k → Nat.choose n k = 0`.

If you try to choose more elements than are available, the result is zero.
There are no ways to select $k$ items from a collection of fewer
than $k$ items. -/
TheoremDoc Nat.choose_eq_zero_of_lt as "Nat.choose_eq_zero_of_lt" in "Nat"

NewTheorem Nat.choose_eq_zero_of_lt

/-- The `omega` tactic solves linear arithmetic goals over natural numbers
and integers. It handles equations and inequalities involving `+`, `-`,
`*` (by constants), and `<`, `≤`, `=`. -/
TacticDoc omega

DisabledTactic trivial decide native_decide simp aesop simp_all
