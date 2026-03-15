import GameServer.Commands
import Mathlib

World "SumFormula"
Level 5

Title "The full proof"

Introduction
"
# Gauss's formula: the complete proof

Time to put everything together. Prove:

$$\\forall\\, n,\\quad 2 \\cdot \\sum_{i=0}^{n} i \\;=\\; (n+1) \\cdot n$$

## The proof structure

```
induction n with
| zero => ...        -- base case
| succ n ih => ...   -- inductive step
```

**Base case** ($n = 0$): Both sides are `0`. Use `rfl`.

**Inductive step**: You have
`ih : 2 * (∑ i ∈ range (n + 1), i) = (n + 1) * n`.
1. `rw [Finset.sum_range_succ]` — peel off the last term.
2. `rw [Nat.mul_add]` — distribute the `2`.
3. `rw [ih]` — apply the inductive hypothesis.
4. `ring` — close the algebra.

Steps 1-3 can be combined: `rw [Finset.sum_range_succ, Nat.mul_add, ih]`.
"

/-- Gauss's formula: `2 * (0 + 1 + ... + n) = (n+1) * n`. -/
Statement (n : Nat) :
    2 * (∑ i ∈ Finset.range (n + 1), i) = (n + 1) * n := by
  Hint "Start with `induction n with` to split into base case and
  inductive step."
  induction n with
  | zero =>
    Hint "Base case: both sides are `0`."
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "You have `ih : 2 * (∑ i ∈ range (n + 1), i) = (n + 1) * n`.

    Peel off the last term, distribute the `2`, and apply `ih`:
    `rw [Finset.sum_range_succ, Nat.mul_add, ih]`

    Then close with `ring`."
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Nat.mul_add, ih]`
    followed by `ring`."
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    Hint "The goal is `(n + 1) * n + 2 * (n + 1) = (n + 2) * (n + 1)`.
    Use `ring` to close it."
    Hint (hidden := true) "Use `ring`."
    ring

Conclusion
"
Congratulations! You proved Gauss's formula:

$$\\sum_{i=0}^{n} i = \\frac{n(n+1)}{2}$$

## The complete proof

```
induction n with
| zero => rfl
| succ n ih =>
  rw [Finset.sum_range_succ, Nat.mul_add, ih]
  ring
```

Five lines. Each line corresponds to a clear mathematical step:

1. **`induction n with`** — set up the induction.
2. **`rfl`** — the base case is trivial.
3. **`rw [sum_range_succ, Nat.mul_add, ih]`** — peel off the last term,
   distribute, and apply the hypothesis.
4. **`ring`** — verify the algebra.

## A new tactic: `Nat.mul_add`

You used `Nat.mul_add` to distribute multiplication over addition:
`a * (b + c) = a * b + a * c`. This was necessary to expose the
subexpression `2 * (∑ ...)` so that the inductive hypothesis could
be applied by `rw [ih]`.

## What comes next

The final level asks you to write this proof as a paper proof, completing
the transfer from Lean to ordinary mathematics.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
