import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 4

Title "A Concrete Subset"

Introduction
"
In the last level, you proved `A ⊆ A` where step 3 (proving membership
in the right-hand set) was trivial. Now let us try a concrete example
where step 3 requires real work.

The set of numbers greater than 5 is a subset of the set of numbers
greater than 3. After `intro x hx`, you will have `hx : x ∈ \u007By | y > 5\u007D`
and need to show `x ∈ \u007By | y > 3\u007D`. Both are arithmetic in disguise —
use `change` to reveal them, then `omega` to finish.

This level combines the subset pattern from Level 3 with the
`change`/`omega` tools from Levels 1–2.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num

Statement : ({x : ℕ | x > 5} : Set ℕ) ⊆ {x : ℕ | x > 3} := by
  Hint "Start with the subset pattern: `intro x hx`."
  intro x hx
  Hint "You have `hx : x ∈ \u007By | y > 5\u007D` and need `x ∈ \u007By | y > 3\u007D`.
  Both are arithmetic in disguise. Use `change x > 5 at hx` to reveal the
  hypothesis, then `show x > 3` to reveal the goal."
  change x > 5 at hx
  show x > 3
  Hint "Now you have `hx : x > 5` and need `x > 3`. Use `omega`."
  omega

Conclusion
"
You proved a concrete subset relationship by combining three skills:

1. **Subset pattern**: `intro x hx` to set up the proof.
2. **Definitional unfolding**: `change`/`show` to reveal the arithmetic.
3. **Arithmetic closure**: `omega` to finish.

This is a common pattern in set theory: start with `intro`, unfold
definitions to see what you are really proving, then solve the
underlying logical or arithmetic problem.
"
