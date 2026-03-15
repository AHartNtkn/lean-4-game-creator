import GameServer.Commands
import Mathlib

World "BinomialTheorem"
Level 2

Title "Introducing push_cast"

Introduction
"
# Introducing `push_cast`

When working with binomial coefficients in rings like `ℤ`, `ℚ`, or `ℝ`,
you encounter casts `↑` that convert natural numbers into the target type.
For example, `↑(Nat.choose n k)` casts the binomial coefficient from `ℕ`
to `ℤ`.

The tactic `push_cast` *pushes* casts inward through arithmetic operations:

- `↑(a + b)` becomes `↑a + ↑b`
- `↑(a * b)` becomes `↑a * ↑b`

After `push_cast`, each `↑` sits on a single variable rather than a
compound expression, and `ring` can usually close the goal.

## Your task

Prove that `↑(n * (n + 1)) = ↑n * (↑n + 1)` in `ℤ`.

The left side has a single `↑` wrapping a product. You need `push_cast`
to distribute the cast through `*` and `+`, then `ring` to close.
"

/-- Pushing a cast through a product: ↑(n * (n + 1)) = ↑n * (↑n + 1) in ℤ. -/
Statement (n : ℕ) :
    (↑(n * (n + 1)) : ℤ) = (↑n : ℤ) * ((↑n : ℤ) + 1) := by
  Hint "Use `push_cast` to distribute the cast `↑` through the
  multiplication and addition on the left side.

  Try `push_cast`."
  Hint (hidden := true) "Try `push_cast`."
  push_cast
  Hint "Good! After `push_cast`, each `↑` sits on a single variable.
  The goal is now a polynomial equation in `↑n`.

  Use `ring` to close it."
  Hint (hidden := true) "Try `ring`."
  ring

Conclusion
"
You used `push_cast` followed by `ring` — a common two-step pattern.

## What happened

1. **Before** `push_cast`: `↑(n * (n + 1)) = ↑n * (↑n + 1)`
2. **After** `push_cast`: `↑n * (↑n + 1) = ↑n * (↑n + 1)` —
   the cast was pushed through `*` and `+`, and `↑1` simplified to `1`.
3. **After** `ring`: goal closed.

## The `push_cast` + `ring` pattern

This two-step pattern appears frequently:
```
push_cast   -- normalize casts
ring        -- close the algebraic equation
```

Whenever you see a goal with `↑(complex expression)` on one side
and `↑a * ↑b + ...` on the other, reach for `push_cast` first.

## Another useful tactic: `exact_mod_cast`

Sometimes you already have a proof `h : a = b` in `ℕ`, and need
`↑a = ↑b` in `ℤ`. The tactic `exact_mod_cast h` handles this
automatically — it applies the cast and closes the goal.

## What comes next

The next level applies the binomial theorem in `ℤ`.
"

/-- The `push_cast` tactic pushes coercions `↑` inward through arithmetic
operations like `+`, `*`, and `^`.

For example, `↑(a + b)` becomes `↑a + ↑b`, and `↑(a * b)` becomes `↑a * ↑b`.
This is useful when working with natural number results in `ℤ`, `ℚ`, or `ℝ`. -/
TacticDoc push_cast

NewTactic push_cast
DisabledTactic trivial decide native_decide simp aesop simp_all
