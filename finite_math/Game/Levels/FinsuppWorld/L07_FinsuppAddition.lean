import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 7

Title "Addition of Finsupps: summing over a sum"

Introduction
"
# Summing Over a Sum of `Finsupp`s

In Level 4, you evaluated a sum of `single`s pointwise using `add_apply`.
Now you will compute `Finsupp.sum` over a sum of `Finsupp`s.

## `Finsupp.sum_add_index'`

When you add two `Finsupp`s and then sum, the result distributes:

```
Finsupp.sum_add_index' :
  (∀ a, h a 0 = 0) →
  (∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) →
  (f + g).sum h = f.sum h + g.sum h
```

This says: if `h` sends zero to zero and distributes over addition,
then summing `h` over `f + g` equals summing over `f` plus summing
over `g`.

## Your task

Prove that summing the identity function over `single 1 3 + single 2 5`
gives `3 + 5`.

The proof has two steps:
1. Use `Finsupp.sum_add_index'` to split the sum into two pieces.
2. Use `Finsupp.sum_single_index rfl` to evaluate each piece.
"

/-- The sum of values over `single 1 3 + single 2 5` is `3 + 5`. -/
Statement : ((Finsupp.single 1 (3 : ℕ) + Finsupp.single 2 5) : ℕ →₀ ℕ).sum (fun _ m => m) = 3 + 5 := by
  Hint "Use `rw [Finsupp.sum_add_index']` to split the sum into two pieces.

  This requires two side conditions:
  - `∀ a, h a 0 = 0` — proved by `fun _ => rfl`
  - `∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂` — proved by `fun _ _ _ => rfl`

  So the full call is:
  `rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`."
  Hint (hidden := true) "Try `rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`."
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  Hint "Now the goal is:
  ```
  (single 1 3).sum (fun _ m => m) + (single 2 5).sum (fun _ m => m) = 3 + 5
  ```

  Evaluate each `sum_single_index` on both sides.
  Use `rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]`."
  Hint (hidden := true) "Try `rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]`."
  rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

Conclusion
"
You proved that `Finsupp.sum` distributes over addition of `Finsupp`s.

## The additivity pattern

When working with `Finsupp.sum` on sums, the pattern is:

1. **Split**: `sum_add_index'` decomposes `(f + g).sum h` into
   `f.sum h + g.sum h`, given two mild conditions on `h`.
2. **Evaluate**: `sum_single_index` evaluates each piece when the
   summands are `single`s.

## Side conditions

Both conditions on `h` are natural:
- `h a 0 = 0`: the function does nothing on zero values.
- `h a (b₁ + b₂) = h a b₁ + h a b₂`: the function is additive in
  the value argument.

For `fun _ m => m`, both hold by `rfl` because the identity function
is additive and sends `0` to `0`.

## Algebraic perspective

The fact that `Finsupp.sum` distributes over addition means it is an
additive homomorphism. This is the formal backbone of constructions
like polynomial evaluation: evaluating `p + q` at a point is the
same as evaluating `p` and `q` separately and adding.

**In plain language**: \"Summing over a sum of finitely supported
functions equals summing each one separately and adding the results.\"
"

/-- `Finsupp.sum_add_index'` distributes `Finsupp.sum` over addition:

```
(∀ a, h a 0 = 0) →
(∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂) →
(f + g).sum h = f.sum h + g.sum h
```

**When to use**: When you need to evaluate `Finsupp.sum` on a sum of
`Finsupp`s. Pass the two side conditions as arguments. -/
TheoremDoc Finsupp.sum_add_index' as "Finsupp.sum_add_index'" in "Finsupp"

NewTheorem Finsupp.sum_add_index'
TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
