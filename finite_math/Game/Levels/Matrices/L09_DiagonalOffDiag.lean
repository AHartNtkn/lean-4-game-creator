import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 9

Title "Diagonal Matrix: Off-Diagonal Entry"

Introduction "
# Off-Diagonal Entries Are Zero

A diagonal matrix has `0` at every position where the row and column
indices differ. The key lemma is `Matrix.diagonal_apply_ne`:

```
Matrix.diagonal_apply_ne : i ≠ j → (diagonal d) i j = 0
```

Notice this requires a **proof** that `i ≠ j`. When the indices are
concrete (like `0` and `1`), you can produce this proof with `omega`.

**Your task**: Read an off-diagonal entry of a diagonal matrix.

**Hint**: You will need to establish that the two indices are different
before you can apply `diagonal_apply_ne`. Try building a proof with
`have h : ... := by omega`.
"

/-- Read an off-diagonal entry of a diagonal matrix. -/
Statement (d : Fin 3 → ℤ) : (diagonal d) 0 2 = 0 := by
  Hint "The goal is `(diagonal d) 0 2 = 0`. The indices `0` and `2`
  differ, so this is an off-diagonal entry. You need
  `Matrix.diagonal_apply_ne`, but it requires a proof that `0 ≠ 2`."
  Hint (hidden := true) "Try `have h : (0 : Fin 3) ≠ 2 := by omega`
  to establish the inequality, then `rw [Matrix.diagonal_apply_ne d h]`."
  have h : (0 : Fin 3) ≠ 2 := by omega
  Hint "Now you have `h : 0 ≠ 2`. Use it with `diagonal_apply_ne`."
  Hint (hidden := true) "Try `rw [Matrix.diagonal_apply_ne d h]`."
  rw [diagonal_apply_ne d h]

Conclusion "
Off-diagonal entries of a diagonal matrix are always `0`. To use
`Matrix.diagonal_apply_ne`, you need to supply a proof that the two
indices are different.

The two-step pattern is:
1. `have h : i ≠ j := by omega` — establish the inequality
2. `rw [Matrix.diagonal_apply_ne d h]` — rewrite the entry to `0`

Or in one step: `exact Matrix.diagonal_apply_ne d (by omega)`.

Together with `diagonal_apply_eq` from the previous level, you now
have complete control over reading any entry of a diagonal matrix.

**Vocabulary**: The terms **on-diagonal** (where `i = j`) and
**off-diagonal** (where `i ≠ j`) come up constantly in linear algebra.
Diagonal matrices are exactly the matrices where every off-diagonal
entry is zero.
"

/-- `Matrix.diagonal_apply_ne` evaluates a diagonal matrix off the diagonal:

`i ≠ j → (diagonal d) i j = 0`

When the row and column indices differ, the diagonal matrix returns `0`.

## Syntax
```
rw [Matrix.diagonal_apply_ne d h]     -- where h : i ≠ j
exact Matrix.diagonal_apply_ne d h    -- close the goal directly
exact Matrix.diagonal_apply_ne d (by omega)  -- inline proof
```

## When to use it
When the goal contains `(diagonal d) i j` where you know `i ≠ j`.

## Example
Given `h : (0 : Fin 3) ≠ 2`, the tactic `rw [diagonal_apply_ne d h]`
turns `(diagonal d) 0 2 = 0` into `0 = 0`.

## Warning
You must supply the function `d` and the inequality proof `h` explicitly.
-/
TheoremDoc Matrix.diagonal_apply_ne as "Matrix.diagonal_apply_ne" in "Matrix"

TheoremTab "Matrix"
NewTheorem Matrix.diagonal_apply_ne

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diagonal_apply
