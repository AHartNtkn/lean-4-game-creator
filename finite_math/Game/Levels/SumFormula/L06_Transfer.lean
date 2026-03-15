import GameServer.Commands
import Mathlib

World "SumFormula"
Level 6

Title "Transfer: the paper proof"

Introduction
"
# Transfer: from Lean to paper

You have proved Gauss's formula in Lean. Now let us connect it to the
way you would write this proof in an ordinary mathematics course.

## The paper proof

> **Theorem.** For all $n \\geq 0$, $\\displaystyle\\sum_{i=0}^{n} i
> = \\frac{n(n+1)}{2}$.
>
> *Proof.* By induction on $n$.
>
> **Base case** ($n = 0$): $\\sum_{i=0}^{0} i = 0 = \\frac{0 \\cdot 1}{2}$.
> $\\checkmark$
>
> **Inductive step**: Suppose $\\sum_{i=0}^{n} i = \\frac{n(n+1)}{2}$.
> Then
> $$\\sum_{i=0}^{n+1} i
>   = \\left(\\sum_{i=0}^{n} i\\right) + (n+1)
>   = \\frac{n(n+1)}{2} + (n+1)
>   = \\frac{n(n+1) + 2(n+1)}{2}
>   = \\frac{(n+1)(n+2)}{2}. \\quad\\checkmark$$

## Lean vs. paper correspondence

| Paper step | Lean step |
|------------|-----------|
| \"By induction on $n$\" | `induction n with` |
| Base case: both sides are $0$ | `rfl` |
| Peel off $(n+1)$ | `rw [Finset.sum_range_succ]` |
| Substitute the hypothesis | `rw [ih]` |
| Verify the algebra | `ring` |

## Your final task

Prove the formula one more time. This time, try writing the proof
from memory, thinking of each tactic as corresponding to a step in
the paper proof above.
"

/-- Gauss's formula, one more time. -/
Statement (n : Nat) :
    2 * (∑ i ∈ Finset.range (n + 1), i) = (n + 1) * n := by
  Hint "Write the complete proof. Refer to the paper proof above and
  translate each step:
  1. `induction n with`
  2. Base case: `rfl`
  3. Inductive step: `rw [Finset.sum_range_succ, Nat.mul_add, ih]`
  4. `ring`"
  Hint (hidden := true) "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint (hidden := true) "Try `rw [Finset.sum_range_succ, Nat.mul_add, ih]`
    followed by `ring`."
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    ring

Conclusion
"
Congratulations on completing the **Sum Formula** world!

## What you achieved

You proved the classic formula
$$\\sum_{i=0}^{n} i = \\frac{n(n+1)}{2}$$
and connected the Lean proof to the standard paper proof.

## The journey through this world

1. **L01-L02**: Concrete verification — checking the formula for specific
   values of $n$.
2. **L03**: The base case — both sides are $0$.
3. **L04**: The inductive step — the algebraic core of the proof.
4. **L05**: The complete proof — assembling base case and inductive step.
5. **L06**: Transfer — the paper proof and the Lean-paper correspondence.

## The transfer lesson

Every inductive sum proof in Lean follows the same template:

| Mathematical step | Lean tactic |
|-------------------|-------------|
| Set up induction | `induction n with` |
| Base case (empty sum = 0) | `rfl` |
| Peel off the last term | `rw [sum_range_succ]` |
| Apply inductive hypothesis | `rw [ih]` |
| Verify algebra | `ring` |

If you ever need to prove a sum identity on paper, this same structure
works: state the induction, handle the base case, split off the last
term, substitute the hypothesis, and verify the algebra. The only
difference is whether you write `rw` or \"by the inductive hypothesis\".
"

DisabledTactic trivial decide native_decide simp aesop simp_all
