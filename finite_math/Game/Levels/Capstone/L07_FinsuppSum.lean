import GameServer.Commands
import Mathlib

World "Capstone"
Level 7

Title "Finsupp sum identity"

Introduction
"
# Finsupp meets big operators

In the **FinsuppWorld**, you learned that `Finsupp.sum f h` sums `h a (f a)`
over the support of `f`. In the **BigOpAdvanced** and **FinsetSum** worlds,
you mastered `Finset.sum`.

This level connects the two: decompose the sum of a sum of two
`Finsupp.single` values using `sum_add_index'`, then evaluate each
piece with `sum_single_index`.

## The statement

For `f = single 1 3 + single 2 5` (a finitely supported function that is
`3` at `1`, `5` at `2`, and `0` elsewhere), prove:

$$f.\\text{sum}(\\lambda\\, \\_ \\, m \\mapsto m) = 8$$

## Strategy

1. **`Finsupp.sum_add_index'`** — splits the sum over a sum of `Finsupp`s:
   `(f + g).sum h = f.sum h + g.sum h` (with side conditions).
2. **`Finsupp.sum_single_index`** — evaluates the sum on a `single`:
   `(single a b).sum h = h a b` (with side condition `h a 0 = 0`).

The side conditions for `sum_add_index'` are:
- `∀ a, h a 0 = 0` — proved by `fun _ => rfl`
- `∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ + h a b₂` — proved by `fun _ _ _ => rfl`
"

/-- The Finsupp sum of `single 1 3 + single 2 5` under projection is 8. -/
Statement : (Finsupp.single 1 (3 : ℕ) + Finsupp.single 2 5).sum (fun _ m => m) = 8 := by
  Hint "**Step 1**: Decompose the sum over a sum of `Finsupp`s.

  Use `rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]` to split
  `(f + g).sum h` into `f.sum h + g.sum h`."
  Hint (hidden := true) "Try `rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]`."
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  Hint "**Step 2**: Evaluate each piece.

  Use `rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]`
  to evaluate `(single 1 3).sum h = 3` and `(single 2 5).sum h = 5`."
  Hint (hidden := true) "Try `rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]`."
  rw [Finsupp.sum_single_index rfl, Finsupp.sum_single_index rfl]

Conclusion
"
You connected the **Finsupp** module with **big operators** by:

1. **`sum_add_index'`** — decomposing the sum over a sum of `Finsupp`s.
2. **`sum_single_index`** — evaluating the sum on each `single`.

## The pattern

For any reasonable function `h`:
```
(single a b + single c d).sum h = h a b + h c d
```

This is the `Finsupp` analogue of `∑ x ∈ {a, c}, h x (f x)` —
summing over the support, which is `{a, c}`.

## Why `Finsupp.sum` exists

You might ask: why not just use `Finset.sum` over the support? In fact,
`Finsupp.sum f h = ∑ a ∈ f.support, h a (f a)`. The `Finsupp.sum`
notation is a convenience that bundles the support and function together,
making it easy to decompose sums algebraically (via `sum_add_index'`)
without manually manipulating the support finset.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
