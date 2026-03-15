import GameServer.Commands
import Mathlib

World "Capstone"
Level 2

Title "Warm-up: Counting + big operators"

Introduction
"
# Warm-up: Counting meets big operators

Two of the course's most important modules are **counting** (via
`Fintype.card`) and **big operators** (via `Finset.sum`). This level
asks you to use both.

## Part 1: Counting a product type

`Fintype.card (Fin 3 × Fin 2)` counts the elements of the product
type. You know:

- `Fintype.card_prod` decomposes the cardinality of a product.
- `Fintype.card_fin n` evaluates `Fintype.card (Fin n) = n`.

## Part 2: Summing over Fin 3

`∑ i : Fin 3, (i : ℕ)` sums the values `0, 1, 2`.

- `Fin.sum_univ_three` expands a sum over `Fin 3` into three terms.
- `norm_num` does the arithmetic.

## Your task

Prove both parts as a conjunction.
"

/-- The product `Fin 3 × Fin 2` has 6 elements, and `∑ i : Fin 3, i = 3`. -/
Statement : Fintype.card (Fin 3 × Fin 2) = 6 ∧ ∑ i : Fin 3, (i : ℕ) = 3 := by
  Hint "Split with `constructor`, then handle each part."
  constructor
  · Hint "**Part 1**: Use `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`
    to compute `card (Fin 3 × Fin 2) = 3 * 2 = 6`."
    Hint (hidden := true) "Try `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`."
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  · Hint "**Part 2**: Use `rw [Fin.sum_univ_three]` to expand the sum
    into `(0 : ℕ) + 1 + 2`, then `norm_num` to compute."
    Hint (hidden := true) "Try `rw [Fin.sum_univ_three]` then `norm_num`."
    rw [Fin.sum_univ_three]
    norm_num

Conclusion
"
You retrieved two skills from different parts of the course:

- **Counting**: `Fintype.card_prod` and `Fintype.card_fin` for
  computing cardinalities of compound types.
- **Big operators**: `Fin.sum_univ_three` for expanding a sum over
  a concrete `Fin` type, plus arithmetic.

In ordinary mathematics, $|\\text{Fin } 3 \\times \\text{Fin } 2| = 3 \\cdot 2 = 6$
and $\\sum_{i=0}^{2} i = 0 + 1 + 2 = 3$ are trivial. In Lean, each
requires naming the right lemma. The point is fluency with the API.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
