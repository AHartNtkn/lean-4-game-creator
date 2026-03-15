import GameServer.Commands
import Mathlib

World "FinsuppWorld"
Level 4

Title "A Finsupp nonzero at two points"

Introduction
"
# Building a `Finsupp` Nonzero at Two Points

So far you have worked with `Finsupp.single`, which is nonzero at
exactly one point. How do you build a function nonzero at *two* points?

## Addition of `Finsupp`s

The type `α →₀ M` supports addition (when `M` has addition). Adding
two `Finsupp`s adds their values pointwise:

```
Finsupp.add_apply : (f + g) a = f a + g a
```

So `Finsupp.single 1 3 + Finsupp.single 2 5` is a `Finsupp` that
sends `1` to `3`, sends `2` to `5`, and sends everything else to `0`.

## Evaluation strategy

To evaluate `(f + g) a`:
1. `rw [Finsupp.add_apply]` to split into `f a + g a`.
2. Evaluate each piece with `Finsupp.single_apply` + `if_pos`/`if_neg`.
3. Close the arithmetic (e.g., with `omega`).

## Your task

Prove that `Finsupp.single 1 3 + Finsupp.single 2 5` sends `1` to `3`.

This requires evaluating both `single`s at `1`, then simplifying `3 + 0`.
"

/-- Adding two `single`s and evaluating: `(single 1 3 + single 2 5) 1 = 3`. -/
Statement : ((Finsupp.single 1 (3 : ℕ) + Finsupp.single 2 5) : ℕ →₀ ℕ) 1 = 3 := by
  Hint "Start with `rw [Finsupp.add_apply]` to split the evaluation
  into `(single 1 3) 1 + (single 2 5) 1`."
  rw [Finsupp.add_apply]
  Hint "Now evaluate each `single` at `1`. The first gives `3`
  (since `1 = 1`), the second gives `0` (since `2 ≠ 1`).

  Use `rw [Finsupp.single_apply, if_pos rfl]` for the first,
  then `rw [Finsupp.single_apply, if_neg (by omega)]` for the second."
  Hint (hidden := true) "Try:
  ```
  rw [Finsupp.single_apply, if_pos rfl,
      Finsupp.single_apply, if_neg (by omega)]
  ```"
  rw [Finsupp.single_apply, if_pos rfl, Finsupp.single_apply, if_neg (by omega)]
  Hint (hidden := true) "The goal is `3 + 0 = 3`. Close it with `omega`."
  omega

Conclusion
"
You built a `Finsupp` nonzero at two points by adding two `single`s,
then evaluated it.

## The construction pattern

To build a `Finsupp` nonzero at points $a_1, \\ldots, a_k$ with values
$b_1, \\ldots, b_k$, use:
```
Finsupp.single a₁ b₁ + Finsupp.single a₂ b₂ + ⋯ + Finsupp.single aₖ bₖ
```

To evaluate, use `add_apply` to split, then `single_apply` on each piece.

## Why addition?

Using addition to combine `single`s is natural because `Finsupp` forms
an additive monoid (and an additive group when `M` is one). This means:
- `0 : α →₀ M` is the zero function (sending everything to `0`).
- `f + g` adds pointwise.
- `Finsupp.single a b` is the \"basis element\" at `a` with coefficient `b`.

This additive structure is what makes `Finsupp` useful for representing
free modules, polynomial rings, and similar algebraic constructions.

**In plain language**: \"To build a function nonzero at several points,
add together `single`s — one for each point.\"
"

/-- `Finsupp.add_apply` states that addition of `Finsupp`s is pointwise:

```
(f + g) a = f a + g a
```

**When to use**: To evaluate a sum of `Finsupp`s at a point. Rewrite
with this, then evaluate each summand separately. -/
TheoremDoc Finsupp.add_apply as "Finsupp.add_apply" in "Finsupp"

NewTheorem Finsupp.add_apply
TheoremTab "Finsupp"
DisabledTactic trivial decide native_decide simp aesop simp_all
