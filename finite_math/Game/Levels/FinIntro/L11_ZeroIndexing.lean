import GameServer.Commands
import Mathlib

World "FinIntro"
Level 11

Title "Zero-indexing: Fin.last gives n, not n+1"

Introduction
"
# Confronting the off-by-one

The most common mistake with `Fin n` is thinking its elements run from
`1` to `n`. They don't -- they run from `0` to `n - 1`.

This means:
- `Fin 4` contains `{0, 1, 2, 3}`, **not** `{1, 2, 3, 4}`
- The largest element of `Fin 4` is `3`, not `4`
- `Fin.last 3 : Fin 4` has value `3`

## Your task

Prove that `(Fin.last 3).val ≠ 4`.

This forces you to confront the zero-indexing head-on. `Fin.last 3` is the
largest element of `Fin 4`, but its value is `3`, not `4`. So claiming
its value is `4` leads to a contradiction.

The proof plan:
1. Use `intro h` to assume `(Fin.last 3).val = 4` for contradiction
2. Lean reduces `(Fin.last 3).val` to `3`, giving `h : 3 = 4`
3. Use `omega` to see that `3 = 4` is a contradiction
"

/-- The value of `Fin.last 3` is not `4`. -/
Statement : (Fin.last 3).val ≠ 4 := by
  Hint "Assume the opposite: `intro h` gives you `h : (Fin.last 3).val = 4`."
  intro h
  Hint "Lean reduces `(Fin.last 3).val` to `3`, so `h : 3 = 4`. This is a
  contradiction. Try `omega`."
  omega

Conclusion
"
The relationship is: in `Fin n`, the largest value is `n - 1`, and
`Fin.last (n - 1)` has value `n - 1`. The type index `n` is always
one more than the maximum value.

This zero-indexing convention matches array indexing in programming:
an array of size `n` has valid indices `0, 1, ..., n - 1`. If you try
to access index `n`, you are out of bounds.

Later in this course, you will see that `Finset.range n` also follows
this convention: it contains `{0, 1, ..., n - 1}`, not `{1, 2, ..., n}`.
In fact, there is a deep connection between `Fin n` and `Finset.range n` --
each element of `range n` corresponds to an element of `Fin n`. You will
explore this in the big-operator worlds (W13+), where sums over
`Finset.range n` and sums indexed by `Fin n` are interchangeable.
"
