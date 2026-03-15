import GameServer.Commands
import Mathlib

World "FinThreeExamples"
Level 10

Title "The swap is an involution"

Introduction
"
# Applying a Function Twice

The swap function `0 ↦ 0, 1 ↦ 2, 2 ↦ 1` has a special property:
if you apply it twice, you get back to where you started.

- `f(f(0)) = f(0) = 0`
- `f(f(1)) = f(2) = 1`
- `f(f(2)) = f(1) = 2`

A function with this property is called an **involution**: applying it
twice is the same as doing nothing (the identity).

## Why this matters

Not every bijection is an involution. The cyclic shift `0 ↦ 1, 1 ↦ 2, 2 ↦ 0`
from Levels 4--9 is **not** an involution:

- `f(f(0)) = f(1) = 2 ≠ 0`

Applying the cyclic shift twice gives a different permutation (the
reverse cyclic shift). You need to apply it **three** times to return
to the start. This distinction --- order 2 vs order 3 --- is a
preview of the concept of **order** in group theory.

## Your task

Prove that the swap function is an involution: `f(f(i)) = i` for every
`i : Fin 3`.

Use `intro i`, then `fin_cases i` to split into the three cases.
Each case should close with `rfl` because both sides compute to the
same value.
"

/-- The swap permutation on `Fin 3` is an involution: applying it twice gives the identity. -/
Statement : ∀ i : Fin 3,
    (fun j : Fin 3 => match j with | 0 => (0 : Fin 3) | 1 => 2 | 2 => 1)
    ((fun j : Fin 3 => match j with | 0 => (0 : Fin 3) | 1 => 2 | 2 => 1) i) = i := by
  Hint "Start with `intro i` to pick an arbitrary element of `Fin 3`."
  intro i
  Hint "Use `fin_cases i` to split into the three cases."
  fin_cases i
  · Hint "The goal reduces to `0 = 0` after evaluating `f(f(0)) = f(0) = 0`.
    Close with `rfl`."
    rfl
  · Hint "The goal reduces to `1 = 1` after evaluating `f(f(1)) = f(2) = 1`.
    Close with `rfl`."
    rfl
  · Hint "The goal reduces to `2 = 2` after evaluating `f(f(2)) = f(1) = 2`.
    Close with `rfl`."
    rfl

DisabledTactic trivial decide native_decide simp aesop simp_all omega norm_num

Conclusion
"
The swap function is an involution: `f(f(i)) = i` for all `i`.

This is a structural property that distinguishes the swap from the
cyclic shift:

| Function | `f(f(0))` | `f(f(1))` | `f(f(2))` | Involution? |
|----------|-----------|-----------|-----------|-------------|
| Swap: `0↦0, 1↦2, 2↦1` | 0 | 1 | 2 | Yes (order 2) |
| Cyclic: `0↦1, 1↦2, 2↦0` | 2 | 0 | 1 | No (order 3) |

The cyclic shift needs to be applied **three** times to return to the
start. The swap needs only **two**. In group theory, this is expressed
by saying the swap has **order 2** and the cyclic shift has **order 3**.

**Connection to composition**: Applying a function twice is the same as
composing it with itself: $f \\circ f$. The involution property says
$f \\circ f = \\text{id}$, i.e., the composition is the identity. Order
is the smallest positive number of compositions that returns to the
identity.

**In plain language**: \"Swapping 1 and 2 twice gets you back to the
original arrangement. But cycling forward twice does not --- you need
to cycle a third time.\"
"
