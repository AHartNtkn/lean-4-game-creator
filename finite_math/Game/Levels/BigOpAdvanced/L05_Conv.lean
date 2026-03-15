import GameServer.Commands
import Mathlib

World "BigOpAdvanced"
Level 5

Title "Introducing conv"

Introduction
"
# The `conv` tactic: rewriting inside a binder

You have used `rw` many times to rewrite equalities. But `rw` operates
on the *entire* goal — it cannot reach inside a `∑` or `∀` binder.

For example, suppose your goal is:
```
∑ i ∈ range n, (i * i) = ∑ i ∈ range n, i ^ 2
```

You know that `i * i = i ^ 2` (by `← sq`), but `rw [← sq]` fails
because `sq` expects a specific variable, and `rw` does not know which
`i` to target.

The **`conv`** tactic solves this. It opens a \"rewriting cursor\" that
you can navigate into sub-expressions:

```
conv_lhs =>     -- focus on the left-hand side
  arg 2         -- enter the second argument (the function ∑ applies)
  ext i         -- introduce the bound variable i
  rw [← sq]     -- rewrite i * i to i ^ 2
```

After the `conv` block closes, the goal has been rewritten.

## The key pattern

For rewriting inside `∑ i ∈ s, f i`:

```
conv_lhs =>   -- or conv_rhs =>
  arg 2       -- the function f
  ext i       -- name the bound variable
  rw [...]    -- rewrite inside
```

## Your task

Prove: `∑ i ∈ range n, (i * i) = ∑ i ∈ range n, i ^ 2`.

Use `conv_lhs` to rewrite `i * i` to `i ^ 2` using `← sq` inside
the sum.
"

/-- Use `conv` to rewrite inside a sum. -/
Statement (n : Nat) :
    ∑ i ∈ Finset.range n, (i * i) = ∑ i ∈ Finset.range n, i ^ 2 := by
  Hint "Use `conv_lhs` to navigate inside the left-hand sum and rewrite
  `i * i` to `i ^ 2`.

  ```
  conv_lhs =>
    arg 2
    ext i
    rw [← sq]
  ```

  The `arg 2` selects the function argument of `∑`, `ext i` introduces
  the bound variable, and `rw [← sq]` rewrites `i * i` to `i ^ 2`."
  Hint (hidden := true) "Try:
  ```
  conv_lhs =>
    arg 2
    ext i
    rw [← sq]
  ```"
  conv_lhs =>
    arg 2
    ext i
    rw [← sq]

Conclusion
"
You used `conv` to rewrite inside a big-operator binder!

## Why `conv` matters

Many big-operator goals require normalizing the expression *inside*
the sum before you can apply lemmas like `sum_add_distrib` or
`mul_sum`. Without `conv`, you would need `sum_congr` with a
pointwise proof — which works, but is heavier. `conv` gives you
a direct, surgical rewrite.

## `conv` vs. `sum_congr`

| Approach | When to use |
|----------|-------------|
| `conv` | Quick, one-step rewrites inside a binder |
| `sum_congr` | When you need a more complex pointwise argument |

Both achieve the same result. `conv` is more convenient for simple
cases; `sum_congr` is more flexible when the pointwise proof requires
multiple steps.

## Transfer

The `conv` tactic has no direct analogue in paper proofs. On paper,
you would simply say \"rewriting each term\" or \"since `a·a = a²`
for each `i`.\" In Lean, `conv` is the mechanism that makes this
possible.

## What comes next

The next level introduces another new tactic: `gcongr`, for monotone
inequality goals.
"

/-- The `conv` tactic lets you navigate into sub-expressions (including
inside binders like `∑` or `∀`) and perform targeted rewrites.

Syntax for rewriting inside `∑ i ∈ s, f i`:
```
conv_lhs =>
  arg 2
  ext i
  rw [lemma]
```
`conv_rhs` targets the right-hand side instead. -/
TacticDoc conv

NewTactic conv
DisabledTactic trivial decide native_decide simp aesop simp_all
