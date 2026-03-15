import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 4

Title "Interchanging summation order"

Introduction
"
# `Finset.sum_comm`: swapping a double sum

In ordinary mathematics, you freely interchange the order of
summation in a double sum:

$$\\sum_{i=0}^{n-1} \\sum_{j=0}^{m-1} f(i, j) =
\\sum_{j=0}^{m-1} \\sum_{i=0}^{n-1} f(i, j)$$

In Lean, this is `Finset.sum_comm`:

```
Finset.sum_comm {s : Finset γ} {t : Finset α} {f : γ → α → β} :
  ∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y
```

This is a powerful tool: many combinatorial identities become easy
once you interchange the order of summation.

## Your task

Prove that a double sum over `range 3 × range 4` can be reordered.

Use `exact Finset.sum_comm` or `rw [Finset.sum_comm]`.
"

/-- Interchanging summation order. -/
Statement (f : Nat → Nat → Nat) :
    ∑ i ∈ Finset.range 3, ∑ j ∈ Finset.range 4, f i j =
    ∑ j ∈ Finset.range 4, ∑ i ∈ Finset.range 3, f i j := by
  Hint "The two sides differ only in the order of summation. Use
  `Finset.sum_comm` to swap them.

  Try `exact Finset.sum_comm`."
  Hint (hidden := true) "Try `exact Finset.sum_comm`."
  exact Finset.sum_comm

Conclusion
"
You interchanged the summation order using `Finset.sum_comm`.

## When to use `sum_comm`

Use `sum_comm` when:
- You have a double sum `∑ i, ∑ j, f i j` and the inner sum is hard
  to evaluate in the current order.
- Swapping the order makes one of the sums collapse (e.g., because the
  inner sum becomes a constant or a known closed form).
- You need to match a different formulation of the same identity.

## A classic application

The identity
$$\\sum_{i=0}^{n-1}\\sum_{j=0}^{n-1} \\min(i, j) =
\\sum_{j=0}^{n-1}\\sum_{i=0}^{n-1} \\min(i, j)$$

looks trivial by `sum_comm`, but interchanging the summation order is
often the key first step in a much harder proof.

## Transfer

In ordinary mathematics, swapping summation order over finite sums is
always legal — it is a consequence of commutativity and associativity
of addition. In Lean, this is captured by the `AddCommMonoid` structure.

## What comes next

The next level introduces the `conv` tactic, which lets you rewrite
*inside* a big-operator binder.
"

/-- `Finset.sum_comm` states that
`∑ x ∈ s, ∑ y ∈ t, f x y = ∑ y ∈ t, ∑ x ∈ s, f x y`.

The order of summation in a double sum can be interchanged. -/
TheoremDoc Finset.sum_comm as "Finset.sum_comm" in "Finset"

NewTheorem Finset.sum_comm
DisabledTactic trivial decide native_decide simp aesop simp_all
