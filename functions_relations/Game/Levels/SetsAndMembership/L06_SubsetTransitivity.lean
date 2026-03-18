import GameServer.Commands
import Game.Metadata
import Mathlib.Data.Set.Basic

World "SetsAndMembership"
Level 6

Title "Subset Transitivity"

Introduction
"
If `A ⊆ B` and `B ⊆ C`, then `A ⊆ C`. This is the **transitivity** of
the subset relation, and it requires chaining two subset hypotheses.

The proof starts like any subset proof: `intro x hx` to assume `x ∈ A`.
Then you need to get from `x ∈ A` to `x ∈ C` by going through `B`.

You have two hypotheses at your disposal:
- `h1 : A ⊆ B` — feeding it `hx : x ∈ A` gives `x ∈ B`
- `h2 : B ⊆ C` — feeding it a proof of `x ∈ B` gives `x ∈ C`

This is your first multi-step subset proof. You will need to use one
subset hypothesis to produce an intermediate fact, then feed that
fact to the second hypothesis.
"

DisabledTactic trivial decide native_decide simp aesop simp_all tauto norm_num
DisabledTheorem Set.Subset.trans le_trans

Statement (A B C : Set ℕ) (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C := by
  Hint "Start with the standard subset opening: `intro x hx`."
  intro x hx
  Hint "You have `hx : x ∈ A`, `h1 : A ⊆ B`, and `h2 : B ⊆ C`.
  First, use `h1` to get from `A` to `B`. Try `have hxB := h1 hx`
  to create an intermediate fact."
  have hxB := h1 hx
  Hint "Now you have `hxB : x ∈ B`. Use `h2` to get to `C`.
  Try `exact h2 hxB`."
  exact h2 hxB

Conclusion
"
You proved subset transitivity by chaining two subset applications.

The pattern is clear:

1. `intro x hx` — assume `x ∈ A`
2. `have hxB := h1 hx` — deduce `x ∈ B` from the first subset
3. `exact h2 hxB` — deduce `x ∈ C` from the second subset

You could also compress this into a single line: `exact h2 (h1 hx)`.
The expression `h2 (h1 hx)` reads as 'apply h2 to the result of
applying h1 to hx' — which is exactly the chain `A → B → C`.

This chaining pattern appears constantly in set theory proofs.
"
