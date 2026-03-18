import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 2

Title "Set-Builder Notation"

Introduction
"
In the last level you used `show` to reveal what a set membership goal
really means. But what about hypotheses? If you have a hypothesis
`hx : x ∈ \u007By | P y\u007D`, it *looks* like set membership, but it
*is* the proposition `P x`.

The **`change`** tactic lets you replace a goal *or a hypothesis* with a
definitionally equal expression. Unlike `show` (which only works on the
goal), `change` can modify hypotheses using the `at` keyword.

**New tactic**: `change` — replaces a goal or hypothesis with a
definitionally equal form. Use `change P at h` to modify hypothesis `h`.

In this level, you have a hypothesis about membership in a set-builder
set, and you need to use it to prove membership in a different set.
Use `change` to reveal what both sides really mean, then finish the proof.
"

/-- The `change` tactic replaces a goal or hypothesis with a definitionally
equal expression. Unlike `show` (which only works on the goal), `change`
can also modify hypotheses.

## Syntax
- `change <expression>` — replaces the current goal
- `change <expression> at h` — replaces hypothesis `h`

## When to use
Use `change` when a hypothesis or goal involves set membership notation
that obscures the underlying proposition. For example, if `hx : x ∈ \u007By | P y\u007D`,
then `change P x at hx` rewrites the hypothesis to `hx : P x`. -/
TacticDoc «change»

NewTactic «change»

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement (x : ℕ) (hx : x ∈ ({y : ℕ | y > 5} : Set ℕ)) :
    x ∈ ({y : ℕ | y > 3} : Set ℕ) := by
  Hint "You have `hx : x ∈ \u007By | y > 5\u007D` and need to show `x ∈ \u007By | y > 3\u007D`.
  Both are really arithmetic propositions in disguise.
  Try `change x > 5 at hx` to reveal what `hx` really says."
  change x > 5 at hx
  Hint "Good — now `hx : x > 5`. The goal is still `x ∈ \u007By | y > 3\u007D`.
  Use `change x > 3` (or `show x > 3`) to reveal the goal."
  change x > 3
  Hint "Now both sides are plain arithmetic. Use `omega` to finish."
  omega

Conclusion
"
You now have two tools for seeing through set membership notation:

- **`show`** replaces the *goal* with a definitionally equal form.
- **`change`** replaces the *goal or a hypothesis* with a definitionally equal form.

These tactics do not prove anything — they just change how Lean
displays things. But that display change is exactly what you need to
connect set-theoretic language to the underlying logic.

**Note**: If you tried `omega` directly on the original goal, it would
have failed. `omega` works on arithmetic goals, but it cannot see through
set membership notation. You need `show` or `change` first to reveal
the arithmetic.

**Recipe**: When a set membership hypothesis or goal hides an arithmetic
or logical fact, use `change` (or `show`) to reveal it, then solve the
revealed problem directly.
"
