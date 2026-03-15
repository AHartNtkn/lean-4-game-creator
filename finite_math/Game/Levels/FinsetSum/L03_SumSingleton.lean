import GameServer.Commands
import Mathlib

World "FinsetSum"
Level 3

Title "sum_singleton with a function"

Introduction
"
# Practicing `sum_singleton` with a function

You used `Finset.sum_singleton` in Level 1. Let's practice with
an explicit function argument. Recall the lemma:

```
Finset.sum_singleton (f : α → β) (a : α) : ∑ x ∈ {a}, f x = f a
```

## Your task

Given a function `f : Nat → Nat` and a natural number `a`, prove:

```
∑ x ∈ {a}, f x = f a
```

This is a direct application of `sum_singleton`.
"

/-- The sum of `f` over a singleton is `f a`. -/
Statement (f : Nat → Nat) (a : Nat) :
    ∑ x ∈ ({a} : Finset Nat), f x = f a := by
  Hint "This is a direct application of `Finset.sum_singleton`.
  Use `rw [Finset.sum_singleton]` or `exact Finset.sum_singleton f a`."
  Hint (hidden := true) "Try `exact Finset.sum_singleton f a`."
  exact Finset.sum_singleton f a

Conclusion
"
You applied `Finset.sum_singleton` with an explicit function.

## The pattern

When you see `∑ x ∈ {a}, f x`, you can always rewrite it to `f a`.
This works for *any* function `f` and *any* element `a`.

Note: `sum_singleton` is stated for a general `AddCommMonoid`, not
just `Nat`. You will see it work for integers, rationals, and other
number types throughout this course.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
