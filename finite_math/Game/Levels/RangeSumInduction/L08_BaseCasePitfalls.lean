import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 8

Title "Base case pitfalls"

Introduction
"
# Base case: `range 0 = ∅`

In every inductive sum proof so far, the base case was just `rfl`.
That worked because Lean's kernel can see that `∑ i ∈ range 0, f i`
reduces to `0`.

But why does it reduce? Let us spell it out.

## The base case, step by step

The base case goal is always:

```
∑ i ∈ Finset.range 0, f i = 0
```

The key facts are:
- **`Finset.range_zero`**: `range 0 = ∅`
- **`Finset.sum_empty`**: `∑ x ∈ ∅, f x = 0`

So you can always prove the base case by:

```
rw [Finset.range_zero, Finset.sum_empty]
```

Understanding this mechanism matters: if the right-hand side does not
reduce to `0` at `n = 0`, you may need `range_zero` + `sum_empty`
explicitly, followed by arithmetic.

## Your task

Prove that the sum over `range 0` is `0` for *any* function
`f : Nat → Nat`.

Use `intro f` to introduce the function, then rewrite with
`Finset.range_zero` and `Finset.sum_empty`.
"

/-- The sum over `range 0` is always zero, regardless of the function. -/
Statement : ∀ f : Nat → Nat, ∑ i ∈ Finset.range 0, f i = 0 := by
  Hint "First introduce the function with `intro f`."
  intro f
  Hint "Now rewrite `range 0` to `∅` and the empty sum to `0`.
  Use `rw [Finset.range_zero, Finset.sum_empty]`."
  Hint (hidden := true) "Try `rw [Finset.range_zero, Finset.sum_empty]`."
  rw [Finset.range_zero, Finset.sum_empty]

Conclusion
"
You proved that `∑ i ∈ range 0, f i = 0` for any function `f`.

## Why this matters

The base case of any inductive sum proof is always trivial: the sum
over an empty range is `0`. The two lemmas that make this work are:

- `Finset.range_zero : range 0 = ∅`
- `Finset.sum_empty : ∑ x ∈ ∅, f x = 0`

In practice, `rfl` usually closes the base case automatically. But
knowing the mechanism helps when:
- You need to debug a proof that is not closing.
- The right-hand side at `n = 0` does not reduce to `0` by itself.
- You want to write a transparent `calc` proof.

## Ready for the boss

You now have all the tools:
- `induction n with` to set up the proof
- `rfl` or `rw [range_zero, sum_empty]` for the base case
- `rw [sum_range_succ, ih]` for the inductive step
- `ring` or `omega` to close the arithmetic
- `calc` for explicit step-by-step reasoning

The boss will test them all.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
