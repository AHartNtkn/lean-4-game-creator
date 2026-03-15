import GameServer.Commands
import Mathlib

World "FinsetTransformations"
Level 4

Title "Image witnesses in a harder case"

Introduction
"
# Finding the right witness

In the last level, the witness was obvious: `3` doubles to `6`.
This time the function is less transparent, so you will need to
think about which element maps to the target.

## Your task

Consider the function `f(x) = x² + 1` applied to {0, 1, 2, 3}.
Prove that `5` belongs to the image.

You need to find `a ∈ {0, 1, 2, 3}` with `a² + 1 = 5`. Since
`2² + 1 = 5`, the witness is `2`.

## Reminder

The proof shape is:
1. `rw [Finset.mem_image]` to expose the existential.
2. `use 2` to provide the witness.
3. Prove `2 ∈ {0, 1, 2, 3}` and `2² + 1 = 5`.
"

/-- `5` belongs to the image of {0, 1, 2, 3} under `x ↦ x² + 1`. -/
Statement : (5 : Nat) ∈ Finset.image (fun x => x ^ 2 + 1) ({0, 1, 2, 3} : Finset Nat) := by
  Hint "Rewrite with `Finset.mem_image` to see the existential."
  Hint (hidden := true) "Use `rw [Finset.mem_image]`."
  rw [Finset.mem_image]
  Hint "Provide the witness. Which element of the source finset maps
  to `5` under `x ↦ x² + 1`?"
  Hint (hidden := true) "Use `use 2` since `2² + 1 = 5`."
  use 2
  Hint "Now prove the conjunction: membership in the source finset
  and the equation `2² + 1 = 5`."
  Hint (hidden := true) "Use `constructor`, then
  `simp [Finset.mem_insert, Finset.mem_singleton]` and `norm_num`."
  constructor
  · simp [Finset.mem_insert, Finset.mem_singleton]
  · norm_num

Conclusion
"
Good. The proof pattern is the same as Level 3, but the witness
required a moment of thought. This is the heart of image reasoning:
**you must identify which pre-image maps to the target**.

In later levels, we will see that `Finset.image` can produce finsets
that are **smaller** than the source -- because the function might
send two different inputs to the same output. The existential in
`mem_image` hides this: it asks only for **one** witness, even if
multiple exist.
"

DisabledTactic trivial decide native_decide aesop simp_all
