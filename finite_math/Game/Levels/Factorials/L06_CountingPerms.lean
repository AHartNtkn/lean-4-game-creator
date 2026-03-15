import GameServer.Commands
import Mathlib

World "Factorials"
Level 6

Title "Counting permutations"

Introduction
"
# Factorials count permutations

A **permutation** of a set is a bijection from the set to itself —
a rearrangement of its elements. The number of permutations of an
$n$-element set is $n!$.

## In Lean

Lean represents permutations of a type `α` as `Equiv.Perm α`,
which is the type of bijections from `α` to `α`. Mathlib provides:

```
Fintype.card_perm {α : Type} [DecidableEq α] [Fintype α] :
  Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial
```

This says: the number of permutations of `α` equals
`(Fintype.card α)!`.

For `Fin n`, we also need:

```
Fintype.card_fin (n : ℕ) : Fintype.card (Fin n) = n
```

## Your task

Prove that the number of permutations of `Fin 3` (a 3-element set)
is 6.

## Strategy

1. Use `Fintype.card_perm` to rewrite the count of permutations
   as `(Fintype.card (Fin 3)).factorial`.
2. Use `Fintype.card_fin` to simplify `Fintype.card (Fin 3)` to `3`.
3. Compute `3! = 6` using `factorial_succ` and `factorial_zero`.
"

/-- There are exactly 6 permutations of a 3-element set. -/
Statement : Fintype.card (Equiv.Perm (Fin 3)) = 6 := by
  Hint "Start with `rw [Fintype.card_perm]` to express the count
  of permutations in terms of factorial."
  Hint (hidden := true) "Try `rw [Fintype.card_perm]`."
  rw [Fintype.card_perm]
  Hint "The goal is now `(Fintype.card (Fin 3)).factorial = 6`.

  Use `rw [Fintype.card_fin]` to simplify `Fintype.card (Fin 3)` to `3`."
  Hint (hidden := true) "Try `rw [Fintype.card_fin]`."
  rw [Fintype.card_fin]
  Hint "The goal is now `Nat.factorial 3 = 6`. Compute it by
  unfolding the recursion with `Nat.factorial_succ` and `Nat.factorial_zero`,
  just as you did in Level 1."
  Hint (hidden := true) "Try:
  ```
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_zero]
  ```"
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_zero]

Conclusion
"
You proved that $|\\mathrm{Perm}(\\mathrm{Fin}\\;3)| = 3! = 6$.

## Why this matters

This is the beginning of *counting with structure*. The factorial
function is not just an abstract recursion — it counts concrete
combinatorial objects:

- **$n!$** = number of ways to arrange $n$ objects in a line
- **$n^{\\underline{k}}$** = number of ways to choose and arrange $k$
  objects from $n$

We will explore these connections further in later worlds on
binomial coefficients and counting arguments.

## Transfer moment

On paper you would write: \"The number of permutations of
$\\{0, 1, 2\\}$ is $3! = 6$, since each of the 3 positions can
be filled by any of the remaining elements.\" The Lean proof
replaces this combinatorial argument with a definitional
computation.

## What comes next

The boss level integrates everything: you will prove the general
identity $n! = \\prod_{i=0}^{n-1}(i+1)$ by induction.
"

/-- `Fintype.card_perm` states that the number of permutations of a
finite type `α` equals `(Fintype.card α)!`.

`Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial` -/
TheoremDoc Fintype.card_perm as "Fintype.card_perm" in "Fintype"

NewTheorem Fintype.card_perm
DisabledTactic trivial decide native_decide simp aesop simp_all
