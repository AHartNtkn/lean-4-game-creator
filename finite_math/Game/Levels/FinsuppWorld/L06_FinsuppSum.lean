import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 6

Title "Finsupp.sum: summing over the support"

Introduction
"
# `Finsupp.sum`: The Big Operator for `Finsupp`

You already know how to sum a function over a `Finset` using `∑`. The
type `Finsupp` has its own summation operation that is tailored to
finitely supported functions.

## `Finsupp.sum`

Given `f : α →₀ M` and `h : α → M → N`, the expression `f.sum h`
sums `h a (f a)` over all `a` in `f.support`:

```
f.sum h = ∑ a ∈ f.support, h a (f a)
```

This is like a big operator, but it uses the `Finsupp`'s own support
as the index set.

## The key evaluation rule

For `Finsupp.single`, summing is simple:

```
Finsupp.sum_single_index :
  h a 0 = 0 → (Finsupp.single a b).sum h = h a b
```

This says: if `h` sends `(a, 0)` to `0` (a natural condition for any
\"reasonable\" operation), then summing `h` over `single a b` just gives
`h a b` — because the only nonzero point is `a`, with value `b`.

## Your task

Compute `(Finsupp.single 3 5).sum (fun _ m => m)`.

The function `fun _ m => m` extracts the value, ignoring the point.
So this sum is just the value at the only nonzero point: `5`.

Use `exact Finsupp.sum_single_index rfl`, where `rfl` proves the
side condition `(fun _ m => m) 3 0 = 0`.
"

/-- Summing the identity function over `single 3 5` gives `5`. -/
Statement : (Finsupp.single 3 (5 : ℕ)).sum (fun _ m => m) = 5 := by
  Hint "Use `exact Finsupp.sum_single_index rfl`.

  The lemma `sum_single_index` requires a proof that `h a 0 = 0`. Here
  `h = fun _ m => m`, so `h 3 0 = 0` is just `0 = 0`, which is `rfl`."
  Hint (hidden := true) "Try `exact Finsupp.sum_single_index rfl`."
  exact Finsupp.sum_single_index rfl

Conclusion
"
You computed a sum over a `Finsupp.single` using `sum_single_index`.

## Why the side condition?

The lemma `sum_single_index` requires `h a 0 = 0`. This ensures that
if the value at `a` were `0`, the sum would be `0` — matching the
convention that `single a 0 = 0` (the zero `Finsupp`).

In practice, this condition is almost always trivially satisfied:
- `fun _ m => m` satisfies it because `0 = 0`.
- `fun a m => a * m` satisfies it because `a * 0 = 0`.
- `fun _ m => m ^ 2` satisfies it because `0 ^ 2 = 0`.

## Connection to big operators

`Finsupp.sum` is Mathlib's way of summing over a finitely supported
function without having to explicitly name the support as a `Finset`.
It is used heavily in the definitions of polynomial evaluation,
free modules, and formal power series.

**In plain language**: \"Summing over a `Finsupp` means summing over
its support. For a `single`, there is only one term.\"
"

/-- `Finsupp.sum f h` sums `h a (f a)` over the support of `f`:

```
f.sum h = ∑ a ∈ f.support, h a (f a)
```

**Key evaluation rule**: `Finsupp.sum_single_index` evaluates this
for `Finsupp.single`. -/
DefinitionDoc Finsupp.sum as "Finsupp.sum"

/-- `Finsupp.sum_single_index` evaluates `Finsupp.sum` on a `single`:

```
h a 0 = 0 → (Finsupp.single a b).sum h = h a b
```

The side condition `h a 0 = 0` is typically closed by `rfl` or `ring`.

**When to use**: Whenever you need to evaluate `Finsupp.sum` on a
`Finsupp.single`. -/
TheoremDoc Finsupp.sum_single_index as "Finsupp.sum_single_index" in "Finsupp"

NewDefinition Finsupp.sum
NewTheorem Finsupp.sum_single_index
TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
