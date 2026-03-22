import Game.Metadata

World "FinTuples"
Level 12

Title "ext for Functions"

Introduction "
# Extensionality for Functions

In MeetFin, you used `ext` to prove two `Fin` elements are
equal by showing their underlying values are equal. Now you'll
use `ext` in a new context: **functions**.

For functions, extensionality says:

> Two functions are equal if and only if they agree on every input.

In symbols: $f = g \\iff \\forall\\, i,\\; f(i) = g(i)$.

When the goal is `f = g` where `f g : Fin n → α`, using
`ext i` introduces `i : Fin n` and changes the goal to `f i = g i`.

This is the same `ext` tactic, just applied to a different type.
In MeetFin, `ext` decomposed `Fin` equality into value equality.
Here, `ext` decomposes function equality into pointwise equality.

**Your task**: Prove `f = g` given that they agree on every input.
"

/-- Two functions that agree everywhere are equal. -/
Statement (f g : Fin 3 → ℕ) (h : ∀ i, f i = g i) :
    f = g := by
  Hint "Use `ext i` to introduce an index `i : Fin 3` and
  reduce the goal to `f i = g i`."
  ext i
  Hint "The goal is `f i = g i`. The hypothesis `{h}` says
  `∀ i, f i = g i`. Use `exact h i`."
  exact h i

Conclusion "
The pattern is simple:

1. `ext i` — reduce function equality to pointwise equality
2. Prove `f i = g i` for the introduced `i`

This is the same tactic you used in MeetFin for `Fin` elements.
Both are instances of the same principle: two composite objects
are equal when their components are equal.

Note: the tactic `funext i` does the same thing as `ext i`
for functions. Both are valid.
"

/-- `ext` reduces equality of composite objects to equality of their components.

## For Fin elements
When the goal is `a = b` where `a b : Fin n`, `ext` reduces it to
`a.val = b.val` — two `Fin` values are equal when their underlying
natural numbers are equal.

## For functions
When the goal is `f = g` where `f g : α → β`, `ext i` introduces
a variable `i : α` and reduces the goal to `f i = g i` — two
functions are equal when they agree on every input.

## For finsets
When the goal is `s = t` where `s t : Finset α`, `ext x` introduces
a variable `x : α` and reduces the goal to `x ∈ s ↔ x ∈ t` — two
finsets are equal when they have the same elements (extensionality).

All are instances of the same principle: two composite objects are
equal when their components are equal.
-/
TacticDoc ext

DisabledTactic trivial decide native_decide simp aesop simp_all fin_cases interval_cases norm_num
DisabledTheorem funext
