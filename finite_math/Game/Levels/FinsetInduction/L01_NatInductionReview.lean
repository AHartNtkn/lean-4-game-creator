import GameServer.Commands
import Mathlib

World "FinsetInduction"
Level 1

Title "Recalling Nat induction"

Introduction
"
# Finset induction and cardinality proofs

Welcome to the **Finset Induction** world. This world introduces a new
induction principle — one for *finsets* rather than natural numbers — and
shows how to use it to prove cardinality results.

## Starting point: Nat induction

You already know induction on natural numbers from the Natural Number Game.
The pattern is:

```
induction n with
| zero => ...       -- base case: prove P 0
| succ n ih => ...  -- inductive step: assume P n, prove P (n + 1)
```

Every natural number is either `zero` or `succ n` for some `n`, so if you
cover both cases you have proved `P n` for all `n`.

## Your task

As a warm-up, prove `0 + n = n` by induction on `n`.

- **Base case**: `0 + 0 = 0`, which is `rfl`.
- **Inductive step**: assume `0 + n = n`, prove `0 + (n + 1) = n + 1`.
  Use `rw [Nat.add_succ]` to unfold `0 + (n + 1)` to `(0 + n) + 1`,
  then `rw [ih]` to apply the inductive hypothesis.
"

/-- `0 + n = n` by induction on `n`. -/
Statement (n : Nat) : 0 + n = n := by
  Hint "Start with `induction n with` to split into the base case and
  inductive step."
  induction n with
  | zero =>
    Hint "The base case is `0 + 0 = 0`. This is true by definition."
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "The goal is `0 + (n + 1) = n + 1`. You have `ih : 0 + n = n`.
    First, unfold `0 + (n + 1)` using `rw [Nat.add_succ]`, then
    apply the inductive hypothesis with `rw [ih]`."
    Hint (hidden := true) "Use `rw [Nat.add_succ, ih]`."
    rw [Nat.add_succ, ih]

Conclusion
"
You proved `0 + n = n` by Nat induction — a familiar pattern.

## The two pieces of Nat induction

1. **Base case** (`zero`): prove the property for `0`.
2. **Inductive step** (`succ`): assume the property for `n`, prove it for `n + 1`.

This works because every natural number is built by starting at `0` and
applying `succ` repeatedly.

## What comes next

In the next level, you will see a *different* induction principle — one
for **finsets**. Instead of building up from `0` by adding `1`, you build
up from `∅` by inserting elements. The structure is analogous, but the
objects are different.

**In plain language**: \"Induction on natural numbers works because every
natural number is either zero or a successor. We will see that finsets
have an analogous structure: every finset is either empty or obtained by
inserting an element into a smaller finset.\"
"

/-- `Nat.add_succ` states that `n + succ m = succ (n + m)`.

This unfolds addition by one step on the right. -/
TheoremDoc Nat.add_succ as "Nat.add_succ" in "Nat"

NewTheorem Nat.add_succ
DisabledTactic trivial decide native_decide aesop simp_all omega
