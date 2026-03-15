import GameServer.Commands
import Mathlib

World "RangeSumInduction"
Level 4

Title "Setting up calc"

Introduction
"
# The `calc` tactic

In the last level, the inductive step was just `rw [sum_range_succ, ih]`.
But in harder proofs, the arithmetic after rewriting may not be
immediate. The `calc` tactic lets you chain equalities step by step,
making each intermediate equality visible and provable separately.

## How `calc` works

A `calc` block looks like this:

```
calc left-hand side
    = intermediate₁ := by justification₁
  _ = intermediate₂ := by justification₂
  _ = right-hand side := by justification₃
```

Each line starts with `_` (meaning \"the previous right-hand side\")
and provides a justification. You can use `rw`, `ring`, `omega`, or
any other tactic after `:= by`.

## Your task

Prove `∑ i ∈ range n, 1 = n` again, but this time use `calc` in the
inductive step to make the chain of equalities explicit:

```
calc ∑ i ∈ range (n + 1), 1
    = (∑ i ∈ range n, 1) + 1 := by rw [sum_range_succ]
  _ = n + 1 := by rw [ih]
```
"

/-- The sum of `n` ones is `n`, proved with `calc`. -/
Statement (n : Nat) : ∑ i ∈ Finset.range n, 1 = n := by
  Hint "Start with `induction n with`."
  induction n with
  | zero =>
    Hint (hidden := true) "Use `rfl`."
    rfl
  | succ n ih =>
    Hint "Now use a `calc` block to chain the equalities:
    ```
    calc ∑ i ∈ Finset.range (n + 1), 1
        = (∑ i ∈ Finset.range n, 1) + 1 := by rw [Finset.sum_range_succ]
      _ = n + 1 := by rw [ih]
    ```"
    Hint (hidden := true) "Type the full `calc` block as shown in the hint."
    calc ∑ i ∈ Finset.range (n + 1), 1
        = (∑ i ∈ Finset.range n, 1) + 1 := by rw [Finset.sum_range_succ]
      _ = n + 1 := by rw [ih]

Conclusion
"
You used `calc` to lay out the chain of equalities explicitly.

## When to use `calc`

For simple sums like this one, `rw [sum_range_succ, ih]` is shorter.
But `calc` shines when:
- The arithmetic in the inductive step requires multiple steps.
- You want to make the algebra readable.
- You need to apply `ring` or `omega` at a specific step.

In the next levels, `calc` will become more useful as the formulas
grow more complex.
"

/-- The `calc` tactic lets you write a chain of equalities (or
inequalities) step by step:

```
calc a
    = b := by justification₁
  _ = c := by justification₂
  _ = d := by justification₃
```

Each intermediate step is proved separately. The underscore `_` refers
to the right-hand side of the previous line.

`calc` also supports `≤`, `<`, `≥`, `>` and mixed chains. -/
TacticDoc «calc»

NewTactic «calc»
DisabledTactic trivial decide native_decide simp aesop simp_all
