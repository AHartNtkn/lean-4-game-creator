import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 4

Title "Diagonal matrices"

Introduction
"
# `Matrix.diagonal`: Diagonal Matrices

A **diagonal matrix** has nonzero entries only on the main diagonal.
Mathlib provides `Matrix.diagonal` to construct one:

```
Matrix.diagonal (d : n → α) : Matrix n n α
```

Given a function `d : n → α`, it builds the square matrix whose
`(i, j)` entry is `d i` when `i = j` and `0` otherwise.

## The evaluation rule

The key lemma is `Matrix.diagonal_apply`:

```
Matrix.diagonal_apply : Matrix.diagonal d i j = if i = j then d i else 0
```

This reduces entry access on a diagonal matrix to an `if`-`then`-`else`.

## Simplifying the conditional

After `rw [Matrix.diagonal_apply]`, you will see a goal like:

```
if i = j then d i else 0 = ...
```

For concrete indices (e.g., `i = 0, j = 0`), `norm_num` can evaluate
the conditional by checking whether `i = j` is true or false.

## Your task

Prove two facts about a diagonal matrix:
- the `(0, 0)` entry equals `d 0`
- the `(0, 1)` entry equals `0`
"

/-- Diagonal entries and off-diagonal entries of `Matrix.diagonal`. -/
Statement : Matrix.diagonal (fun i : Fin 2 => (i.val + 1 : Int)) 0 0 = 1 ∧
    Matrix.diagonal (fun i : Fin 2 => (i.val + 1 : Int)) 0 1 = 0 := by
  Hint "Split the conjunction with `constructor`."
  constructor
  · Hint "Use `rw [Matrix.diagonal_apply]` to unfold the diagonal entry.
    This gives you `if 0 = 0 then ... else 0 = 1`.
    Then `norm_num` evaluates the conditional."
    Hint (hidden := true) "Try `rw [Matrix.diagonal_apply]` then `norm_num`."
    rw [Matrix.diagonal_apply]
    norm_num
  · Hint "Same approach: `rw [Matrix.diagonal_apply]` unfolds the entry.
    Since `0 ≠ 1`, the conditional evaluates to `0`."
    Hint (hidden := true) "Try `rw [Matrix.diagonal_apply]` then `norm_num`."
    rw [Matrix.diagonal_apply]
    norm_num

Conclusion
"
You computed entries of a diagonal matrix using `diagonal_apply`.

## The two cases

| Case | Condition | `diagonal d i j` |
|------|-----------|-------------------|
| Diagonal | `i = j` | `d i` |
| Off-diagonal | `i ≠ j` | `0` |

This is exactly how diagonal matrices work on paper: the main diagonal
carries the values, everything else is zero.

## The identity matrix

The identity matrix `1 : Matrix n n α` satisfies:

```
Matrix.one_apply : (1 : Matrix n n α) i j = if i = j then 1 else 0
```

This is exactly `Matrix.diagonal (fun _ => 1)`. The identity matrix is
a special case of a diagonal matrix!

**In plain language**: \"A diagonal matrix is defined by a function on
the index type. Entry `(i, j)` is the function value when `i = j` and
zero otherwise.\"
"

/-- `Matrix.diagonal d` constructs a square matrix whose `(i, j)` entry
is `d i` when `i = j` and `0` when `i ≠ j`.

**Type**: `(d : n → α) → Matrix n n α`

**Key lemma**: `Matrix.diagonal_apply : Matrix.diagonal d i j = if i = j then d i else 0`

**Special case**: The identity matrix `1` is `Matrix.diagonal (fun _ => 1)`. -/
DefinitionDoc Matrix.diagonal as "Matrix.diagonal"

/-- `Matrix.diagonal_apply` evaluates a diagonal matrix entry:

`Matrix.diagonal d i j = if i = j then d i else 0`

**When to use**: After constructing a diagonal matrix, use this to
reduce entry access to a conditional. Then use `norm_num` or `split`
to evaluate the conditional for concrete indices. -/
TheoremDoc Matrix.diagonal_apply as "Matrix.diagonal_apply" in "Matrix"

NewDefinition Matrix.diagonal
NewTheorem Matrix.diagonal_apply
TheoremTab "Matrix"
DisabledTactic trivial decide native_decide simp aesop simp_all
