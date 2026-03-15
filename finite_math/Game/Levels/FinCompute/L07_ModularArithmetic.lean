import GameServer.Commands
import Mathlib

World "FinCompute"
Level 7

Title "Modular arithmetic surprises"

Introduction
"
# Arithmetic on `Fin n` Is Modular

`Fin n` is not just an index type --- it supports arithmetic operations.
But unlike natural number arithmetic, arithmetic on `Fin n` **wraps around**
modulo `n`.

## Addition wraps

In `Fin 5`:
- `(3 : Fin 5) + (4 : Fin 5) = (2 : Fin 5)` because `3 + 4 = 7 ≡ 2 (mod 5)`

## Subtraction wraps too (and this surprises people!)

In `Fin 5`:
- `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)` because `1 - 3 ≡ -2 ≡ 3 (mod 5)`

On natural numbers, `1 - 3 = 0` (truncated subtraction). But on `Fin 5`,
subtraction wraps around: `1 - 3 = 1 + (5 - 3) = 1 + 2 = 3`.

## Multiplication wraps

In `Fin 4`:
- `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)` because `2 * 3 = 6 ≡ 2 (mod 4)`

You might expect `2 * 3 = 6`, but in `Fin 4`, the result wraps to `2`.

## Your task

Prove the subtraction wrapping fact: `(1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5)`.

This is a concrete computation in `Fin 5`. The `decide` tactic can verify
it by evaluating both sides.
"

/-- Subtraction in `Fin 5` wraps around: `1 - 3 = 3 (mod 5)`. -/
Statement : (1 : Fin 5) - (3 : Fin 5) = (3 : Fin 5) := by
  Hint "This is a concrete computation in `Fin 5`. Try `decide`."
  Hint (hidden := true) "The `decide` tactic evaluates both sides of the equality
  in `Fin 5`. On the left: `1 - 3` in `Fin 5` computes to `3` (wrapping around).
  On the right: `3`. They are equal."
  decide

DisabledTactic native_decide

Conclusion
"
In `Fin 5`, subtraction wraps around: `1 - 3 = 1 + (5 - 3) = 1 + 2 = 3`.

This is **modular arithmetic** --- the same arithmetic you use when
reading a clock. On a 12-hour clock, 3 hours before 1 o'clock is
10 o'clock (wrapping past 0). In `Fin n`, the modulus is `n`.

Key facts about `Fin n` arithmetic:
- Addition is defined as `(a + b) mod n`
- Subtraction wraps: `(a - b + n) mod n`
- Multiplication wraps: `(a * b) mod n`
- `Fin n` with `n ≥ 1` forms a **commutative ring** with these operations
- The zero element is `(0 : Fin n)`

Notice that `decide` handled this easily --- it just evaluated both
sides. For concrete equalities in `Fin n`, `decide` is the right tool.

**Why this matters**: Modular arithmetic on `Fin n` connects finite
types to number theory. In later worlds, when you study permutations
or functions on `Fin n`, understanding this arithmetic structure will
be essential.

**In plain language**: \"Arithmetic in $\\mathbb{Z}/5\\mathbb{Z}$ is
performed modulo 5. Since $1 - 3 \\equiv -2 \\equiv 3 \\pmod{5}$,
we have $1 - 3 = 3$ in this ring.\"
"
