import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 11

Title "Set Extensionality"

Introduction
"
Here is the most important idea in this world: **two sets are equal if
and only if they have the same elements.** This principle is called
**set extensionality**.

In Lean, the **`ext`** tactic turns a goal of the form `A = B` (where
`A` and `B` are sets) into the goal `x ∈ A ↔ x ∈ B` for a fresh
variable `x`. After `ext x`, you have an iff to prove, which you
split with `constructor` and handle each direction.

This gives us the fundamental proof pattern for set equality:

1. `ext x` — reduce equality to membership equivalence
2. `constructor` — split the iff into forward and backward
3. Prove each direction as an implication

This pattern — **ext, constructor, chase** — will be used hundreds of
times in this course. Master it here.

**New tactic**: `ext` — reduces set equality to elementwise equivalence.

**New theorem**: `Set.ext_iff` — states `A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`.
"

/-- The `ext` tactic proves equality of sets (and other extensional structures)
by reducing to pointwise equivalence. If the goal is `A = B` where `A B : Set α`,
then `ext x` introduces a fresh variable `x : α` and changes the goal to
`x ∈ A ↔ x ∈ B`.

## Syntax
`ext x` where `x` is the name for the new variable.

## When to use
Use `ext` whenever you need to prove two sets are equal. Follow it with
`constructor` to split the resulting iff. -/
TacticDoc ext

/-- `Set.ext_iff` states the extensionality principle for sets:
`A = B ↔ ∀ x, x ∈ A ↔ x ∈ B`. Two sets are equal exactly when they have
the same elements.

You rarely need to invoke this theorem directly — the `ext` tactic
applies it automatically. But it is useful to know the statement. -/
TheoremDoc Set.ext_iff as "Set.ext_iff" in "Set"

NewTactic ext
NewTheorem Set.ext_iff

TheoremTab "Set"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement (P Q : ℕ → Prop) (h : ∀ x, P x → Q x) (h' : ∀ x, Q x → P x) :
    ({x : ℕ | P x} : Set ℕ) = {x : ℕ | Q x} := by
  Hint "The goal is to show two sets are equal. Use `ext x` to introduce
  an arbitrary element `x` and reduce the goal to showing `x` is in one
  set iff it is in the other."
  ext x
  Hint "After `ext x`, the goal is `x ∈ \u007Bx | P x\u007D ↔ x ∈ \u007Bx | Q x\u007D`,
  which is `P x ↔ Q x`. Use `constructor` to split the iff into forward
  and backward directions."
  constructor
  · Hint "Forward direction: assume `P x`, prove `Q x`. The hypothesis
    `h : ∀ x, P x → Q x` gives you exactly this. Try `intro hpx`
    then `exact h x hpx`."
    intro hpx
    exact h x hpx
  · Hint "Backward direction: assume `Q x`, prove `P x`. Use `h'`.
    Try `intro hqx` then `exact h' x hqx`."
    intro hqx
    exact h' x hqx

Conclusion
"
You proved your first set equality using extensionality!

Let us translate this into ordinary mathematics:

*To show these two sets are equal, we show they have the same elements.
Take any x. If P(x) holds, then Q(x) holds by hypothesis h. If Q(x)
holds, then P(x) holds by hypothesis h'. So x is in the first set if
and only if it is in the second, and since x was arbitrary, the sets
are equal.*

**The ext pattern**:
1. `ext x` — 'two sets are equal iff they have the same elements'
2. `constructor` — split the iff into forward and backward
3. `intro h` + prove membership — handle each direction

In harder problems, the two directions will require different reasoning.
But the pattern stays the same.
"
