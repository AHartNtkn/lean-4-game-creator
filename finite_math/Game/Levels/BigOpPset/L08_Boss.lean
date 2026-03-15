import GameServer.Commands
import Mathlib

World "BigOpPset"
Level 8

Title "Boss: Multi-step big-operator proof"

Introduction
"
# Boss: Prove a sum identity by induction

Prove by induction:

$$\\sum_{i=0}^{n-1} (2i + 3) \\;=\\; n(n + 2)$$

## Strategy

Use induction on `n`:

- **Base case** ($n = 0$): Both sides are `0`.
- **Inductive step**: Assume `∑ i ∈ range n, (2*i + 3) = n * (n + 2)`.
  Use `sum_range_succ` to peel off the last term `2*n + 3`, apply
  the hypothesis, and close with `ring`.

This integrates V3 (induction), V11 (`sum_range_succ`), and V20
(algebraic manipulation via `ring`).
"

/-- The sum `∑ i ∈ range n, (2 * i + 3) = n * (n + 2)`. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (2 * i + 3) = n * (n + 2) := by
  Hint (hidden := true) "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Both sides are `0`. Use `rfl`."
    rfl
  | succ n ih =>
    Hint (hidden := true) "Peel off the last term with
    `rw [Finset.sum_range_succ]`, then `rw [ih]`, then `ring`."
    rw [Finset.sum_range_succ, ih]
    ring

Conclusion
"
Congratulations on completing the **big-operator problem set**!

You proved:
$$\\sum_{i=0}^{n-1}(2i + 3) = n(n + 2)$$

The proof integrated three skills:

1. **V3 — Induction on range sums**: the overall proof structure.
2. **V11 — `sum_range_succ`**: peeling off the last term to expose
   the inductive hypothesis.
3. **V20 — Algebraic manipulation**: `ring` closed the arithmetic
   in the inductive step.

## What you retrieved in this world

| Level | Skill retrieved | From world |
|-------|----------------|-----------|
| L01 | Inductive sum (V3, V11) | W14 |
| L02 | Inductive product (M25) | W15 |
| L03 | Algebraic manipulation (V20, L7) | W15 |
| L04 | `sum_filter` (M38) | W16 |
| L05 | `sum_comm` for double sums (M26) | W16 |
| L06 | Transfer: read sigma notation (T10) | — |
| L07 | Transfer: write inductive proof (T2) | — |
| L08 | Integration: V3 + V11 + V20 | All |

## Transfer moment

In ordinary mathematics, you would write:

> *Proof by induction on n.* Base case: the empty sum is $0 = 0 \\cdot 2$.
> Inductive step: assume $\\sum_{i=0}^{n-1}(2i+3) = n(n+2)$. Then
> $$\\sum_{i=0}^{n}(2i+3) = n(n+2) + (2n+3) = n^2 + 4n + 3 = (n+1)(n+3).$$

The Lean proof is a direct transcription: `induction`, `sum_range_succ`,
`ih`, `ring`. Every step has a paper counterpart.

## What comes next

The next module covers **combinatorics and counting identities**:
factorials, binomial coefficients, Pascal's rule, and the binomial
theorem.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
