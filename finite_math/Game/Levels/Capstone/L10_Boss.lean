import GameServer.Commands
import Mathlib

World "Capstone"
Level 10

Title "Boss: the grand integration"

Introduction
"
# Boss: The Grand Integration

This is the **final level** of the Finite Mathematics course.

You will prove three facts, each drawing on a different combination of
modules. Together they demonstrate the unity of the finite-math toolkit.

## Part 1: Matrix trace = product cardinality

$$\\text{tr}\\left(\\text{diag}(1, 2, 3)\\right) = |\\text{Fin } 3 \\times \\text{Fin } 2|$$

Both sides equal $6$. The left side uses **matrices** + **big operators** +
**Fin**. The right side uses **Fintype counting**.

**Strategy**: `trace_diagonal` → `sum_univ_three` → `card_prod` + `card_fin` → `norm_num`.

## Part 2: Powerset cardinality = binomial sum

$$|\\mathcal{P}(\\{0,1,2\\})| = \\sum_{k=0}^{3} \\binom{3}{k}$$

Both sides equal $8 = 2^3$. The left side uses **finset** powerset. The
right side uses **binomial coefficients**.

**Strategy**: `card_powerset` + `card_range` → `sum_range_choose`.

## Part 3: Constant sum = product cardinality

$$\\sum_{i \\in \\text{Fin } 3} 2 = |\\text{Fin } 3 \\times \\text{Fin } 2|$$

The left side is a **big operator** over a **Fin** type. The right side is
a **cardinality** computation.

**Strategy**: `sum_const` + `card_univ` + `card_fin` + `smul_eq_mul` → `card_prod` + `card_fin`.

## Your task

Prove all three parts as a conjunction.
"

/-- Three faces of finite mathematics: matrix trace, powerset size,
and constant sums all connect to cardinality. -/
Statement :
    (Matrix.diagonal (fun i : Fin 3 => (i : ℤ) + 1)).trace = ↑(Fintype.card (Fin 3 × Fin 2)) ∧
    (Finset.range 3).powerset.card = ∑ k ∈ Finset.range 4, Nat.choose 3 k ∧
    ∑ _ : Fin 3, (2 : ℕ) = Fintype.card (Fin 3 × Fin 2) := by
  Hint "Start by splitting into three parts with `refine ⟨?_, ?_, ?_⟩`."
  Hint (hidden := true) "Try `refine ⟨?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_⟩
  -- Part 1: Matrix trace = product cardinality
  · Hint "**Part 1**: Matrix trace = product cardinality.

    Step 1: `rw [Matrix.trace_diagonal]` — reduce trace to a sum.
    Step 2: `rw [Fin.sum_univ_three]` — expand the sum.
    Step 3: `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]` — compute the cardinality.
    Step 4: `norm_num` — arithmetic."
    Hint (hidden := true) "Try:
    ```
    rw [Matrix.trace_diagonal, Fin.sum_univ_three]
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    norm_num
    ```"
    rw [Matrix.trace_diagonal, Fin.sum_univ_three]
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    norm_num
  -- Part 2: Powerset cardinality = binomial sum
  · Hint "**Part 2**: Powerset cardinality = binomial sum.

    Step 1: `rw [Finset.card_powerset, Finset.card_range]` — left side becomes `2 ^ 3`.
    Step 2: `rw [Nat.sum_range_choose]` — right side becomes `2 ^ 3`."
    Hint (hidden := true) "Try `rw [Finset.card_powerset, Finset.card_range, Nat.sum_range_choose]`."
    rw [Finset.card_powerset, Finset.card_range]
    rw [Nat.sum_range_choose]
  -- Part 3: Constant sum = product cardinality
  · Hint "**Part 3**: Constant sum = product cardinality.

    Step 1: `rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]` — left side becomes `3 * 2 = 6`.
    Step 2: `rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]` — right side becomes `3 * 2 = 6`."
    Hint (hidden := true) "Try:
    ```
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    ```"
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]

Conclusion
"
# Congratulations!

You have completed the **Finite Mathematics** course.

## What you just proved

Three equations, each connecting different parts of the course:

| Part | Left side | Right side | Modules used |
|------|----------|------------|-------------|
| 1 | `trace(diag(1,2,3))` | `card(Fin 3 × Fin 2)` | Matrix + Big-op + Counting |
| 2 | `card(powerset(range 3))` | `∑ C(3,k)` | Finset + Binomial |
| 3 | `∑ 2 over Fin 3` | `card(Fin 3 × Fin 2)` | Big-op + Counting |

## What you learned in this world

| Level | What you did | Modules integrated |
|-------|-------------|-------------------|
| L01 | Fin bounds + Finset cardinality | Fin + Finset |
| L02 | Product cardinality + sum over Fin | Counting + Big-op |
| L03 | Constant sum = card × constant | Big-op + Counting |
| L04 | Pigeonhole on a product type | Pigeonhole + Counting + Fin |
| L05 | Powerset card = binomial sum | Finset + Binomial |
| L06 | Matrix trace computation | Matrix + Big-op + Fin |
| L07 | Finsupp sum decomposition | Finsupp + Big-op |
| L08 | Transfer: the toolkit | Reflection |
| L09 | Transfer: paper proof | Formal ↔ informal |
| L10 | Boss: grand integration | All modules |

## What you learned in the entire course

Over 24 worlds, you built and exercised a comprehensive toolkit for
reasoning about finite mathematical objects in Lean 4:

- **Finite types** (`Fin n`, `Fintype`, `Finset`) — the foundational layer
- **Counting** (cardinality, pigeonhole, inclusion-exclusion) — the quantitative layer
- **Big operators** (`∑`, `∏`, splitting, reindexing) — the computational layer
- **Combinatorics** (factorials, binomial coefficients, the binomial theorem) — the identity layer
- **Advanced structures** (finsupp, permutations, matrices) — the application layer

Each layer builds on the ones below it. Matrices use big operators.
Big operators use finsets. Finsets use finite types. And counting
arguments tie them all together.

## Transfer: the lasting skill

The most important thing you take away is not any specific lemma or
tactic. It is the ability to:

1. **Recognize** which module a problem belongs to.
2. **Choose** the right tool from a large inventory.
3. **Compose** tools from different modules into a single proof.
4. **Translate** between formal and informal arguments.

These skills work in Lean. They work on paper. They work in any
future mathematics you encounter.

**Thank you for playing. Well done.**
"

DisabledTactic trivial decide native_decide simp aesop simp_all
