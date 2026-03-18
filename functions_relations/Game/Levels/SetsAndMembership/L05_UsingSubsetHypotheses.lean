import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 5

Title "Using Subset Hypotheses"

Introduction
"
In the last two levels you proved subset relationships. Now you will
*use* one.

If you have `h : A ⊆ B` and `hx : x ∈ A`, then `h` is really
a function: it takes a proof that `x ∈ A` and produces a proof that
`x ∈ B`. You can feed it the evidence directly with `exact h hx`
or with `apply h`.

But there is a more readable approach: the **`specialize`** tactic.
Writing `specialize h hx` replaces the hypothesis `h` in place, changing
it from `h : A ⊆ B` (which is `∀ x, x ∈ A → x ∈ B`) to
`h : x ∈ B` by feeding it the specific element and its membership proof.

**New tactic**: `specialize` — applies a universal hypothesis to specific
arguments, replacing the hypothesis with the resulting statement.

In this level, you have `h : A ⊆ B` and `hx : x ∈ A`. Use `specialize`
to extract the consequence, then close the goal.
"

/-- The `specialize` tactic applies a universal or implication hypothesis to
specific arguments, replacing the hypothesis with the resulting statement.

## Syntax
`specialize h a₁ a₂ ...`

## Example
If `h : ∀ x, x ∈ A → x ∈ B` and `hx : x ∈ A`, then
`specialize h hx` changes `h` to `h : x ∈ B`.

## When to use
Use `specialize` when you have a `∀` or `→` hypothesis and want to
apply it to specific values. This is especially useful with subset
hypotheses. -/
TacticDoc specialize

NewTactic specialize

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement (A B : Set ℕ) (h : A ⊆ B) (x : ℕ) (hx : x ∈ A) : x ∈ B := by
  Hint "You have `h : A ⊆ B` and `hx : x ∈ A`. The hypothesis `h` is
  really `∀ x, x ∈ A → x ∈ B`. Try `specialize h hx` to feed it
  the proof that `x ∈ A`."
  specialize h hx
  Hint "Now `h : x ∈ B`, which is exactly the goal. Use `exact h`."
  exact h

Conclusion
"
The `specialize` tactic is a natural way to use universal hypotheses.
When `h : A ⊆ B` and you have `hx : x ∈ A`, writing `specialize h hx`
'feeds' the evidence to `h`, transforming it into `h : x ∈ B`.

You could also have skipped `specialize` entirely and written
`exact h hx` — since `h` applied to `hx` directly produces a proof
of `x ∈ B`. Both approaches are correct; `specialize` is more readable
when proofs get longer.

**Two ways to use a subset hypothesis**:
- `specialize h hx` then `exact h` (step-by-step)
- `exact h hx` (direct application)
"
