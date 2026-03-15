import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 5

Title "Counting permutations = n!"

Introduction
"
# Counting Permutations

How many permutations does a finite type have? The answer is a
classical result: a type with $n$ elements has exactly $n!$ permutations.

## `Fintype.card_perm`

Mathlib formalizes this as:

```
Fintype.card_perm : Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial
```

This says: the number of elements of `Equiv.Perm α` (i.e., the order
of the symmetric group) equals the factorial of the number of elements
of `α`.

## Connecting to `Fin n`

For `Fin n`, we know `Fintype.card (Fin n) = n` (from `Fintype.card_fin`).
So:

$$|S_n| = |\\mathrm{Perm}(\\mathrm{Fin}\\;n)| = n!$$

## Your task

Prove that `Fin 4` has exactly 24 permutations.

The strategy:
1. Use `Fintype.card_perm` to express the count as `(Fintype.card (Fin 4)).factorial`.
2. Use `Fintype.card_fin` to simplify `Fintype.card (Fin 4)` to `4`.
3. Compute `4! = 24` by unfolding the factorial recursion.
"

/-- There are exactly 24 permutations of `Fin 4`. -/
Statement : Fintype.card (Equiv.Perm (Fin 4)) = 24 := by
  Hint "Use `rw [Fintype.card_perm]` to express the count as a factorial."
  rw [Fintype.card_perm]
  Hint "Now use `rw [Fintype.card_fin]` to simplify `Fintype.card (Fin 4)` to `4`."
  rw [Fintype.card_fin]
  Hint "The goal is now `Nat.factorial 4 = 24`. Unfold the factorial recursion
  using repeated `Nat.factorial_succ` and `Nat.factorial_zero`.

  Try:
  ```
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_zero]
  ```"
  Hint (hidden := true) "Try `rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_zero]`."
  rw [Nat.factorial_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_zero]

Conclusion
"
You proved that $|S_4| = 4! = 24$.

## The counting argument

On paper, the argument is: to build a permutation of $\\{0, 1, 2, 3\\}$,
you have 4 choices for where to send `0`, then 3 remaining choices for
`1`, then 2 for `2`, and the last element is forced. So the total is
$4 \\times 3 \\times 2 \\times 1 = 24$.

In Lean, `Fintype.card_perm` encapsulates this reasoning, and
`Fintype.card_fin` + the factorial recursion compute the result.

## Review: factorial from the Factorials world

Recall from the Factorials world:
- `Nat.factorial_succ : (n + 1)! = (n + 1) * n!`
- `Nat.factorial_zero : 0! = 1`

These are the same tools you used there — now applied to count
permutations.

**In plain language**: \"The number of permutations of an $n$-element
set is $n!$. Lean's `Fintype.card_perm` is the formal version of this
classical counting result.\"
"

/-- `Fintype.card_perm` states that the number of permutations of a
finite type equals the factorial of its cardinality:

`Fintype.card (Equiv.Perm α) = (Fintype.card α).factorial`

**When to use**: To compute or reason about the size of the symmetric
group. Combine with `Fintype.card_fin` for `Fin n`. -/
TheoremDoc Fintype.card_perm as "Fintype.card_perm" in "Equiv.Perm"

NewTheorem Fintype.card_perm
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
