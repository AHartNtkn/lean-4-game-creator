import GameServer.Commands
import Mathlib

World "FinCompute"
Level 9

Title "Modular multiplication surprise"

Introduction
"
# More Modular Arithmetic: Multiplication and Zero Divisors

In the earlier level, you saw subtraction wrapping in `Fin 5`. Now
let's see multiplication wrapping --- and a genuinely surprising consequence.

In `Fin 4`:
- You might expect `2 * 3 = 6`, but `6 mod 4 = 2`, so
  `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)`.

Even more strikingly:
- `(2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)`, because `4 mod 4 = 0`.

This means `2` is a **zero divisor** in `Fin 4`: a nonzero element whose
product with another nonzero element is zero. This cannot happen in
ordinary arithmetic, where `a * b = 0` implies `a = 0` or `b = 0`.

## Your task

Prove both facts as a conjunction:
1. `(2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)` (multiplication wraps)
2. `(2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)` (zero divisor!)

Use `constructor` to split, then `decide` for each part.
"

/-- Multiplication in `Fin 4` wraps, and `2` is a zero divisor. -/
Statement : ((2 : Fin 4) * (3 : Fin 4) = (2 : Fin 4)) ∧
    ((2 : Fin 4) * (2 : Fin 4) = (0 : Fin 4)) := by
  Hint "The goal is a conjunction. Use `constructor` to split it."
  constructor
  Hint "Each part is a concrete `Fin 4` computation. Use `decide`."
  · decide
  · decide

Conclusion
"
You just proved two surprising facts about `Fin 4`:

1. `2 * 3 = 2`: the product of two nonzero elements equals one of the factors.
2. `2 * 2 = 0`: a nonzero element squared gives zero!

Fact 2 is the most striking. In ordinary arithmetic, `a * b = 0` implies
`a = 0` or `b = 0`. In `Fin 4`, the element `2` is a **zero divisor** ---
it is nonzero, but `2 * 2 = 0`.

This happens because `4` is not prime. In `Fin p` for a prime `p`,
there are no zero divisors --- every nonzero element has a
multiplicative inverse. This is why $\\mathbb{Z}/p\\mathbb{Z}$ is a
field, while $\\mathbb{Z}/4\\mathbb{Z}$ is only a ring.

**Takeaway**: Arithmetic on `Fin n` wraps modulo `n`. When `n` is
composite, you get zero divisors. When `n` is prime, you get a field.
"

DisabledTactic native_decide
