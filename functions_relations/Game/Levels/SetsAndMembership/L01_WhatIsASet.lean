import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 1

Title "What Is a Set?"

Introduction
"
# Sets and Membership

Welcome to the first real world of Functions & Relations!

In Lean, a set is not a separate type. A set of natural numbers is a
*predicate* — a function `ℕ → Prop` that says which elements belong.
Formally, `Set ℕ` is defined as `ℕ → Prop`.

For example, the set of numbers greater than 3 is the predicate
`fun n => n > 3`. Saying '5 is in this set' just means 'the predicate
is true at 5.'

When you see `x ∈ S` in a goal, Lean is really saying `S x` — the
predicate `S` applied to `x`. The **`show`** tactic lets you replace
the goal with a definitionally equal expression, which is perfect for
revealing what set membership really means.

**New tactics**: `show` — replaces the goal with a definitionally equal
form. `omega` — closes arithmetic goals involving natural numbers.

In this level, your goal is `5 ∈ S` where `S` is the set of numbers
greater than 3. Use `show 5 > 3` to reveal the underlying
proposition, then close the arithmetic goal with `omega`.
"

/-- The `show` tactic replaces the current goal with a definitionally equal expression.
If your goal is `x ∈ S` where `S` is defined as a set-builder set, you can write
`show P x` to see the underlying predicate directly.

## Syntax
`show <expression>`

## When to use
Use `show` when the goal is technically correct but displayed in a form that
makes the next step unclear. This is common with set membership goals. -/
TacticDoc «show»

/-- The `omega` tactic closes goals involving natural number or integer
arithmetic. It can prove equalities, inequalities, and divisibility
statements automatically.

## Syntax
`omega`

## When to use
Use `omega` when the goal is a numeric statement like `5 > 3`, `a + b = b + a`,
or `n ≥ 0`. It handles linear arithmetic over `ℕ` and `ℤ`. -/
TacticDoc omega

/-- `Set α` is the type of sets whose elements have type `α`. In Lean, `Set α`
is defined as `α → Prop` — a set is a predicate that says which elements
belong to it. Writing `{x : α | P x}` constructs the set of all `x`
satisfying predicate `P`. -/
DefinitionDoc Set as "Set"

NewTactic «show» omega
NewDefinition Set

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement : (5 : ℕ) ∈ ({x : ℕ | x > 3} : Set ℕ) := by
  Hint "Your goal says `5 ∈ ...`. This looks like set membership,
  but underneath, Lean is asking whether the predicate `fun x => x > 3` is true
  at `5`. Use `show 5 > 3` to reveal the underlying proposition."
  show 5 > 3
  Hint "Now the goal is just `5 > 3`. Use `omega` to close arithmetic goals
  involving natural numbers."
  omega

Conclusion
"
You proved your first set membership statement!

The key insight: `x ∈ S` where `S = \u007By | P y\u007D` is *definitionally equal* to `P x`. The
`show` tactic swaps between these two views. You did not need any
special set theory — just `show` to see through the notation, and then
`omega` for the arithmetic.

**Recipe**: To prove `x ∈ \u007By | P y\u007D`, use `show P x` to reveal the
predicate, then prove the resulting proposition.
"
