import Game.Metadata

World "GroupTutorial"
Level 7

Title "Targeted Rewriting"

Introduction
"
When an expression has multiple products, `rw [mul_assoc]` rewrites the
**first** (leftmost) matching triple it finds, scanning the goal from
left to right. Sometimes that's not the one you want.

To target a specific triple `(a * b) * c`, provide explicit arguments:
`rw [mul_assoc a b c]`. This tells Lean exactly which three elements
to re-bracket.

Similarly, `rw [← mul_assoc a b c]` targets `a * (b * c)` specifically.

In this level, you'll need targeted rewriting because there are two
possible triples for `mul_assoc` to match.

After you solve this level manually, we'll show you a tactic that
handles all of this automatically.
"

/-- The `group` tactic automatically closes goals that follow from the
group axioms. It works by normalizing both sides of an equation to a
canonical form — collecting terms, cancelling inverse pairs, and
simplifying — then checking if the results match.

Example: if the goal is `a⁻¹ * (a * b) = b`, then `group` closes it.

`group` only handles equational reasoning about group elements. It
cannot help with goals involving `∈`, `∀`, subgroup membership, or
anything beyond "this expression equals that expression."

**Warning**: In the next world, `group` will be disabled so you can
practice the axioms manually. Think of it as a reward for understanding,
not a replacement for understanding. -/
TacticDoc group

NewTactic group

TheoremTab "Group"

Statement (G : Type*) [Group G] (a b c : G) :
    (a * b) * (b⁻¹ * c) = a * c := by
  Hint "The goal is `(a * b) * (b⁻¹ * c) = a * c`. You need to get
  `b * b⁻¹` or `b⁻¹ * b` next to each other so you can cancel.

  Start with `rw [mul_assoc]` to strip the outer parentheses."
  Branch
    group
  Branch
    rw [mul_assoc, ← mul_assoc b, mul_inv_cancel, one_mul]
  rw [mul_assoc]
  Hint "Now the goal should be `a * (b * (b⁻¹ * c)) = a * c`.
  You need to re-bracket `b * (b⁻¹ * c)` into `(b * b⁻¹) * c`.

  Since there are nested products, plain `rw [← mul_assoc]` might
  target the wrong triple. Use explicit arguments:
  `rw [← mul_assoc b b⁻¹ c]`."
  rw [← mul_assoc b b⁻¹ c]
  Hint "Now you should see `a * ((b * b⁻¹) * c) = a * c`.
  Cancel `b * b⁻¹` with `mul_inv_cancel`."
  rw [mul_inv_cancel]
  Hint "Now `a * (1 * c) = a * c`. Use `one_mul` to finish."
  rw [one_mul]

Conclusion
"
You just used **targeted rewriting**: `rw [← mul_assoc b b⁻¹ c]` told
Lean exactly which triple to re-bracket. Without the explicit arguments,
Lean might have re-bracketed the wrong part of the expression.

Here's a secret: the tactic `group` can close any goal that follows
from the group axioms automatically. Try replacing your whole proof
with just `group` to see it work.

But don't get too comfortable — in the next world, we'll disable `group`
and ask you to prove things the hard way. The axioms are your real tools.
`group` is the reward for understanding them.
"
