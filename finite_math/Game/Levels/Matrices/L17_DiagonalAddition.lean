import Game.Levels.Matrices.Imports

open Matrix

World "Matrices"
Level 17

Title "Addition of Diagonal Matrices"

Introduction "
# Diagonal Matrices Are Closed Under Addition

Adding two diagonal matrices produces another diagonal matrix: the
diagonal values add, and the off-diagonal entries remain zero.

$$\\text{diagonal}\\,d + \\text{diagonal}\\,e = \\text{diagonal}\\,(d + e)$$

To prove this, you need a **case split** on whether the row and
column indices are equal. On the diagonal (`i = j`), both sides
give `d i + e i`. Off the diagonal (`i != j`), both sides give
`0 + 0 = 0`.

**New tool: `eq_or_ne`**

`eq_or_ne a b` produces a proof of `a = b ∨ a != b`. Use it with
`obtain` to split into cases:

```
obtain rfl | h := eq_or_ne i j
```

This creates two subgoals:
- The `rfl` case: `j` has been replaced by `i` everywhere.
- The `h` case: you have `h : i != j`.

This pattern is essential for diagonal matrix proofs, where the
behavior depends on whether you are at a diagonal or off-diagonal
entry.

**Your task**: Prove that diagonal matrices add component-wise.
"

/-- The sum of two diagonal matrices is the diagonal of the sum. -/
Statement (d e : Fin 3 → ℤ) : diagonal d + diagonal e = diagonal (d + e) := by
  Hint "You need to prove two matrices are equal. Start with `ext i j`."
  Hint (hidden := true) "Try `ext i j`."
  ext i j
  Hint "Now expand the addition on the left with `Matrix.add_apply`."
  Hint (hidden := true) "Try `rw [Matrix.add_apply]`."
  rw [add_apply]
  Hint "The goal is now
  `(diagonal d) i j + (diagonal e) i j = (diagonal (d + e)) i j`.
  The value depends on whether `i = j` (diagonal) or `i != j`
  (off-diagonal). Split into cases with `eq_or_ne`."
  Hint (hidden := true) "Try `obtain rfl | h := eq_or_ne i j`."
  obtain rfl | h := eq_or_ne i j
  -- i = j case
  · Hint "In the `rfl` case, `j` has been replaced by `i`. All three
    diagonal entries are on-diagonal. Use `diagonal_apply_eq` to
    evaluate each one."
    Hint (hidden := true) "Try
    `rw [Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq]`."
    rw [diagonal_apply_eq, diagonal_apply_eq, diagonal_apply_eq]
    Hint "The goal is `d i + e i = (d + e) i`. Function addition is
    pointwise — `(d + e) i` is definitionally `d i + e i`. Use `rfl`."
    Hint (hidden := true) "Try `rfl`."
    rfl
  -- i ≠ j case
  · Hint "You have `h : i != j`. All three entries are off-diagonal.
    Use `diagonal_apply_ne` with `h` for each one."
    Hint (hidden := true) "Try
    `rw [Matrix.diagonal_apply_ne d h, Matrix.diagonal_apply_ne e h, Matrix.diagonal_apply_ne (d + e) h]`.
    After the three rewrites, the goal becomes `0 + 0 = 0`."
    rw [diagonal_apply_ne d h, diagonal_apply_ne e h, diagonal_apply_ne (d + e) h]
    Hint "The goal is `0 + 0 = 0`. The `ring` tactic closes algebraic
    equalities like this — you learned it in the Big Operator Algebra world."
    Hint (hidden := true) "Try `ring`."
    ring

Conclusion "
You proved that diagonal matrices are **closed under addition**: adding
two diagonal matrices produces another diagonal matrix whose diagonal
values are the sums of the original diagonal values.

The proof introduced the `eq_or_ne` case-split pattern:

```
obtain rfl | h := eq_or_ne i j
```

We will call the combination `ext i j` followed by
`obtain rfl | h := eq_or_ne i j` the **diagonal case-split** strategy.
Just as the **peel** strategy (rewrite outermost operation first) is
the standard move for nested operations, the diagonal case-split is
the standard move for proving identities involving diagonal matrices.
You will use it again in the next two levels and in the boss.

In the `rfl` case, Lean substitutes `j` with `i` automatically, so
all `diagonal_apply_eq` rewrites match. In the `h` case, you supply
`h : i != j` to each `diagonal_apply_ne`.

In linear algebra, the set of diagonal matrices forms a
**commutative subalgebra**: it is closed under addition, scalar
multiplication, and matrix multiplication. You just proved the
addition part.
"

/-- `eq_or_ne a b` produces a proof of `a = b ∨ a ≠ b`.

Use with `obtain` to split into cases:
```
obtain rfl | h := eq_or_ne i j
```
- In the `rfl` case, `j` is replaced by `i` everywhere.
- In the `h` case, you have `h : i ≠ j`.

## When to use it
When a proof requires different reasoning depending on whether two
values are equal or not — especially for diagonal vs. off-diagonal
entries in matrix proofs.
-/
TheoremDoc eq_or_ne as "eq_or_ne" in "Logic"

TheoremTab "Matrix"
NewTheorem eq_or_ne

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num fin_cases interval_cases by_cases tauto linarith nlinarith unfold delta
DisabledTheorem Matrix.diag_diagonal Matrix.diagonal_transpose Matrix.diagonal_add Matrix.diagonal_apply
