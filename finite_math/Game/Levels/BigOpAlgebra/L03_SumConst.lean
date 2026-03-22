import Game.Metadata

World "BigOpAlgebra"
Level 3

Title "Constant Sums Meet Linearity"

Introduction "
# Constant Sums: ∑ c = card • c

What happens when you sum the same value over every element?

$$\\sum_{x \\in s} c = |s| \\cdot c$$

Each of the `|s|` elements contributes `c`, so the total is
`|s|` times `c`. In Lean:

```
Finset.sum_const (c : M) : ∑ x ∈ s, c = s.card • c
```

The `•` symbol is **scalar multiplication** (pronounced
\"n-smul\"). For natural numbers, `n • m` is the same as
`n * m` — it means \"add `m` to itself `n` times.\"

**Connection to card_eq_sum_ones**: You already know
`s.card = ∑ x ∈ s, 1` from BigOpIntro. That's `sum_const`
with `c = 1`, since `s.card • 1 = s.card`.

**Explicit arguments**: When using `exact Finset.sum_const c`,
you must provide the constant `c` explicitly. Lean can't always
infer it. With `rw [Finset.sum_const]`, Lean usually infers `c`
from the goal.

**Your task**: Split `∑(f + 3)` using `sum_add_distrib`, then
simplify the constant part with `sum_const`.
"

/-- Combine sum_add_distrib and sum_const. -/
Statement (s : Finset ℕ) (f : ℕ → ℕ) (hf : ∑ x ∈ s, f x = 20) :
    ∑ x ∈ s, (f x + 3) = 20 + s.card • 3 := by
  Hint "First split the summand `f x + 3` into two sums using
  `rw [Finset.sum_add_distrib]`."
  rw [Finset.sum_add_distrib]
  Hint "The goal now has `∑ x ∈ s, 3` — a constant sum. Use
  `rw [Finset.sum_const]` to convert it to `s.card • 3`."
  Hint (hidden := true) "Try `rw [Finset.sum_const]`."
  rw [Finset.sum_const]
  Hint "Now substitute the known sum with `rw [hf]`."
  rw [hf]

Conclusion "
You combined two tools:
1. `sum_add_distrib` split `∑(f + c)` into `∑f + ∑c`
2. `sum_const` simplified `∑c` to `card • c`

This **split-simplify-substitute** pattern — split the summand
with a big-operator lemma, simplify each piece, substitute known
values — recurs throughout this world and beyond. You'll see it
in at least six more levels.

`sum_const` converts any constant sum into a multiplication by
cardinality — after it, the big operator disappears and you're
left with ordinary arithmetic.

**The `•` notation**: For natural numbers, `n • m` is the same
as `n * m`. The theorem connecting them is `smul_eq_mul`. You
won't need it in this world, but if you ever see `card • c` in
a goal and want `card * c`, that's the bridge.

**When to use it**: Whenever the summand doesn't depend on the
variable — every element contributes the same value.
"

/-- `Finset.sum_const` states that `∑ x ∈ s, c = s.card • c`.

The sum of a constant function equals the cardinality times the
constant. For ℕ, `n • m = n * m`.

## Syntax
```
exact Finset.sum_const c   -- explicit argument needed
rw [Finset.sum_const]      -- Lean infers c from goal
```

## When to use it
When the summand doesn't depend on the variable — every element
contributes the same value `c`.

## Connection
`Finset.card_eq_sum_ones` is the special case with `c = 1`.
-/
TheoremDoc Finset.sum_const as "Finset.sum_const" in "BigOp"

NewTheorem Finset.sum_const

DisabledTactic trivial «decide» native_decide simp aesop simp_all fin_cases interval_cases norm_num by_cases tauto linarith ring ring_nf omega
DisabledTheorem Finset.sum_pair Finset.prod_pair Finset.sum_eq_card_nsmul Finset.sum_nsmul
