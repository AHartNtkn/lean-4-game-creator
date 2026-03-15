import GameServer.Commands
import Mathlib

World "MatrixWorld"
Level 6

Title "Matrix multiplication via Finset.sum"

Introduction
"
# Matrix Multiplication: The Big-Operator Connection

This is the level where everything comes together: matrix multiplication
is defined using **finite sums** — the `∑` operator you mastered in
the big-operator worlds.

## The definition

For matrices `A : Matrix l m α` and `B : Matrix m n α`, the product
`A * B : Matrix l n α` has entries:

$$(A \\cdot B)_{ik} = \\sum_{j} A_{ij} \\cdot B_{jk}$$

In Lean:

```
Matrix.mul_apply : (A * B) i k = ∑ j, A i j * B j k
```

The sum ranges over all `j : m` (the shared index type).

## Unfolding the sum for `Fin 2`

When the shared index type is `Fin 2`, the sum has exactly two terms.
The lemma `Fin.sum_univ_two` unfolds it:

```
Fin.sum_univ_two : ∑ i : Fin 2, f i = f 0 + f 1
```

So for $2 \\times 2$ matrices:

$$(A \\cdot B)_{ik} = A_{i0} \\cdot B_{0k} + A_{i1} \\cdot B_{1k}$$

## Your task

Show that `(A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0` for
arbitrary $2 \\times 2$ integer matrices.
"

/-- Matrix multiplication at entry `(0, 0)` unfolds to a two-term sum. -/
Statement (A B : Matrix (Fin 2) (Fin 2) Int) :
    (A * B) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
  Hint "Start with `rw [Matrix.mul_apply]` to expand `(A * B) 0 0` into
  `∑ j, A 0 j * B j 0`.

  Then `rw [Fin.sum_univ_two]` unfolds the sum over `Fin 2` into two terms:
  `A 0 0 * B 0 0 + A 0 1 * B 1 0`."
  Hint (hidden := true) "Try `rw [Matrix.mul_apply, Fin.sum_univ_two]`."
  rw [Matrix.mul_apply]
  Hint "Good! Now the goal is `∑ j, A 0 j * B j 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0`.

  Use `rw [Fin.sum_univ_two]` to unfold the sum."
  rw [Fin.sum_univ_two]

Conclusion
"
You expanded a matrix product entry using `mul_apply` and `sum_univ_two`.

## The two key lemmas

| Lemma | What it does |
|-------|-------------|
| `Matrix.mul_apply` | Expands `(A * B) i k` into `∑ j, A i j * B j k` |
| `Fin.sum_univ_two` | Unfolds `∑ i : Fin 2, f i` into `f 0 + f 1` |

Together, they turn matrix multiplication into concrete arithmetic.

## The big-operator connection

Matrix multiplication is a **sum over a finite type**. Everything you
learned about `∑` — distributivity, commutativity, reindexing — applies
to matrix products. This is why matrices live naturally in the
finite-mathematics toolkit.

## In ordinary mathematics

On paper, you write:
$$(AB)_{ik} = \\sum_{j=0}^{m-1} a_{ij} b_{jk}$$

In Lean, `Matrix.mul_apply` is exactly this formula, and
`Fin.sum_univ_two` is the computation rule for $m = 2$.

**In plain language**: \"Matrix multiplication is a finite sum. The
entry `(i, k)` of the product sums `A i j * B j k` over all shared
indices `j`.\"
"

/-- `Matrix.mul_apply` expands a matrix product entry:

`(A * B) i k = ∑ j, A i j * B j k`

**When to use**: To unfold matrix multiplication into a finite sum.
Follow with `Fin.sum_univ_two` (or `Fin.sum_univ_three`, etc.) to
expand the sum for concrete index types. -/
TheoremDoc Matrix.mul_apply as "Matrix.mul_apply" in "Matrix"

/-- `Fin.sum_univ_two` unfolds a sum over `Fin 2`:

`∑ i : Fin 2, f i = f 0 + f 1`

**When to use**: After `Matrix.mul_apply` expands a product entry
into `∑ j, ...`, use this to turn the sum into explicit terms when
the index type is `Fin 2`. -/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "Matrix"

NewTheorem Matrix.mul_apply Fin.sum_univ_two
TheoremTab "Matrix"
DisabledTactic trivial decide native_decide simp aesop simp_all
