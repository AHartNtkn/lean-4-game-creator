import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 7

Title "Transfer: Write an inductive sum proof"

Introduction
"
## Level 7: Transfer — Writing an inductive sum proof on paper

Prove the sum-of-constants identity by induction:

$$\\sum_{i=0}^{n-1} 5 \\;=\\; 5n$$

The Lean proof is short: induction, peel, close. The real lesson is
in the conclusion, where you will see the **paper translation** of
this proof.
"

/-- The sum of `n` fives is `5 * n`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 5 = 5 * n := by
  Hint (hidden := true) "Use `induction n with`, then `rfl` for the
  base case, and `rw [Finset.sum_range_succ, ih]; ring` for the step."
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

Conclusion
"
You proved `∑ i ∈ range n, 5 = 5n` in four lines of Lean. Now
let us write the same proof on paper.

## The paper proof

> **Claim.** For all $n \\ge 0$, $\\displaystyle\\sum_{i=0}^{n-1} 5 = 5n$.
>
> **Proof.** By induction on $n$.
>
> *Base case* ($n = 0$): The sum over an empty range is $0$, and
> $5 \\cdot 0 = 0$. ✓
>
> *Inductive step*: Assume $\\sum_{i=0}^{n-1} 5 = 5n$. Then
> $$\\sum_{i=0}^{n} 5 = \\left(\\sum_{i=0}^{n-1} 5\\right) + 5
> = 5n + 5 = 5(n+1).$$
> ∎

## Lean ↔ Paper correspondence

| Lean step | Paper step |
|-----------|-----------|
| `induction n with` | \"By induction on $n$\" |
| `rfl` | Base case: both sides are $0$ |
| `rw [sum_range_succ]` | Peel off the last term |
| `rw [ih]` | Apply the inductive hypothesis |
| `ring` | Algebraic simplification |

**Transfer check**: You can now translate a Lean inductive sum proof
to a standard paper proof. This retrieves T2.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
