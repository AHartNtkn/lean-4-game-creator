import GameServer.Commands
import Mathlib

World "PermutationWorld"
Level 3

Title "Composition of permutations"

Introduction
"
# Composing Permutations

Permutations can be **composed**: if $\\sigma$ and $\\tau$ are permutations,
then $\\sigma \\cdot \\tau$ is the permutation that first applies $\\tau$,
then applies $\\sigma$.

## Multiplication in `Equiv.Perm`

In Lean, `Equiv.Perm α` has a group structure. The multiplication
`σ * τ` composes the two permutations:

```
Equiv.Perm.mul_def : σ * τ = Equiv.trans τ σ
```

**Warning**: the order is reversed! `σ * τ` means \"first apply `τ`,
then apply `σ`.\" This matches the convention in algebra where
$(\\sigma \\tau)(x) = \\sigma(\\tau(x))$.

After rewriting with `mul_def`, use `Equiv.trans_apply` to evaluate:

```
Equiv.trans_apply : (Equiv.trans f g) x = g (f x)
```

So `(σ * τ) x = σ (τ x)`, which you compute by first evaluating `τ x`,
then evaluating `σ` at the result.

## Your task

Compose the swaps `(0 1)` and `(1 2)` on `Fin 3`, and evaluate
the composition at `0`.

The computation: `((0 1) * (1 2))(0)` first applies `(1 2)` to `0`.
Since `0 ≠ 1` and `0 ≠ 2`, the swap `(1 2)` fixes `0`. Then we
apply `(0 1)` to `0`, getting `1`.

So `((0 1) * (1 2))(0) = 1`.
"

/-- Composing swaps `(0 1)` and `(1 2)` and evaluating at `0` gives `1`. -/
Statement : (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2) (0 : Fin 3) = 1 := by
  Hint "Start with `rw [Equiv.Perm.mul_def]` to unfold the multiplication
  into `Equiv.trans`. Then use `rw [Equiv.trans_apply]` to evaluate the
  composition at `0`."
  rw [Equiv.Perm.mul_def]
  Hint "Now use `rw [Equiv.trans_apply]` to split the evaluation into
  two steps: first apply the inner permutation, then the outer one."
  rw [Equiv.trans_apply]
  Hint "The goal is now `(Equiv.swap 0 1) ((Equiv.swap 1 2) 0) = 1`.

  First evaluate `(Equiv.swap 1 2) 0`. Since `0 ≠ 1` and `0 ≠ 2`,
  use `Equiv.swap_apply_of_ne_of_ne` to show this equals `0`.

  Try: `rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)]`."
  rw [Equiv.swap_apply_of_ne_of_ne (by omega : (0 : Fin 3) ≠ 1) (by omega : (0 : Fin 3) ≠ 2)]
  Hint "The goal is now `(Equiv.swap 0 1) 0 = 1`. This is `swap_apply_left`."
  Hint (hidden := true) "Try `rw [Equiv.swap_apply_left]`."
  rw [Equiv.swap_apply_left]

Conclusion
"
You computed the composition of two transpositions at a point.

## The evaluation pattern for compositions

To evaluate `(σ * τ) x`:

1. `rw [Equiv.Perm.mul_def]` — unfold multiplication to `Equiv.trans`.
2. `rw [Equiv.trans_apply]` — split into `σ (τ x)`.
3. Evaluate `τ x` using the swap rules.
4. Evaluate `σ` at the result.

## What is `(0 1) * (1 2)` as a permutation?

If you compute all three values:
- `0 ↦ 1` (as you just proved)
- `1 ↦ 2` (since `(1 2)` sends `1 ↦ 2`, then `(0 1)` fixes `2`)
- `2 ↦ 0` (since `(1 2)` sends `2 ↦ 1`, then `(0 1)` sends `1 ↦ 0`)

So `(0 1) * (1 2)` is the **3-cycle** sending $0 \\mapsto 1 \\mapsto 2 \\mapsto 0$.
This illustrates a key fact: products of transpositions generate all permutations.

**In plain language**: \"To compose permutations, apply them right-to-left.
Lean's `mul_def` and `trans_apply` let you break this into individual
swap evaluations.\"
"

/-- `Equiv.Perm.mul_def` unfolds multiplication of permutations:

`σ * τ = Equiv.trans τ σ`

Note the reversal: `σ * τ` means \"first apply `τ`, then apply `σ`.\"

**When to use**: As the first step when evaluating a product of
permutations at a point. Follow with `Equiv.trans_apply`. -/
TheoremDoc Equiv.Perm.mul_def as "Equiv.Perm.mul_def" in "Equiv.Perm"

/-- `Equiv.trans_apply` evaluates a composition of equivalences:

`(Equiv.trans f g) x = g (f x)`

**When to use**: After `Equiv.Perm.mul_def`, to split the evaluation
of a product into two steps. -/
TheoremDoc Equiv.trans_apply as "Equiv.trans_apply" in "Equiv.Perm"

NewTheorem Equiv.Perm.mul_def Equiv.trans_apply
TheoremTab "Equiv.Perm"
DisabledTactic trivial decide native_decide simp aesop simp_all
