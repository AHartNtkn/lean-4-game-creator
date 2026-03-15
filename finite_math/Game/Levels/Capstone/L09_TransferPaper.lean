import GameServer.Commands
import Mathlib

World "Capstone"
Level 9

Title "Transfer: a paper proof"

Introduction
"
# Transfer: Write the proof on paper

This level asks you to prove a statement in Lean and then read the
proof as a paper argument.

## The statement

For any $n$, summing the constant $1$ over all elements of `Fin n`
gives $n$:

$$\\sum_{i \\in \\text{Fin } n} 1 = n$$

## The paper proof

> *Proof.* The sum $\\sum_{i=0}^{n-1} 1$ has $n$ terms, each equal to
> $1$. By the constant-sum rule, the result is $n \\cdot 1 = n$. $\\square$

## The Lean proof

In Lean, the \"constant-sum rule\" is `Finset.sum_const`, and \"$n$ terms\"
comes from `Finset.card_univ` + `Fintype.card_fin`. The \"$n \\cdot 1 = n$\"
step uses `smul_eq_mul` + `mul_one`.

## Your task

Prove `∑ _ : Fin n, (1 : ℕ) = n`. Each Lean step corresponds to a
sentence in the paper proof above.
"

/-- Summing 1 over all elements of `Fin n` gives `n`. -/
Statement (n : ℕ) : ∑ _ : Fin n, (1 : ℕ) = n := by
  Hint "**Step 1** (\"The sum has constant terms\"):
  Use `rw [Finset.sum_const]` to convert to `card • 1`."
  Hint (hidden := true) "Try `rw [Finset.sum_const]`."
  rw [Finset.sum_const]
  Hint "**Step 2** (\"The number of terms is $n$\"):
  Use `rw [Finset.card_univ, Fintype.card_fin]` to get `n • 1 = n`."
  Hint (hidden := true) "Try `rw [Finset.card_univ, Fintype.card_fin]`."
  rw [Finset.card_univ, Fintype.card_fin]
  Hint "**Step 3** (\"$n \\cdot 1 = n$\"):
  Use `rw [smul_eq_mul, mul_one]` to finish."
  Hint (hidden := true) "Try `rw [smul_eq_mul, mul_one]`."
  rw [smul_eq_mul, mul_one]

Conclusion
"
## The correspondence

| Paper proof | Lean step |
|-------------|----------|
| \"each term is 1\" | `Finset.sum_const` |
| \"there are $n$ terms\" | `card_univ` + `card_fin` |
| \"$n \\cdot 1 = n$\" | `smul_eq_mul` + `mul_one` |

## Why this matters

When you write a Lean proof and can translate each step into a sentence
of ordinary mathematics, you are doing real mathematics — not just
syntax manipulation. The Lean proof is a *formalization* of the paper
proof, not a different activity.

This ability to move between formal and informal proof is the deepest
skill this course teaches. It will serve you in every future mathematics
course, whether or not you use Lean.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
