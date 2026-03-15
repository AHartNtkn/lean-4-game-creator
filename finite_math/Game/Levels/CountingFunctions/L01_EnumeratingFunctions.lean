import GameServer.Commands
import Mathlib

World "CountingFunctions"
Level 1

Title "There are 9 functions from Fin 2 to Fin 3"

Introduction
"
# How Many Functions `Fin 2 → Fin 3`?

Welcome to an example world where you will concretely explore the
functions between two small finite types.

## The setup

A function `f : Fin 2 → Fin 3` assigns to each of the 2 inputs (0 and 1)
one of the 3 possible outputs (0, 1, or 2). How many such functions
are there?

Think of it as filling in a table:

| Input | Output |
|-------|--------|
|   0   |  ?     |
|   1   |  ?     |

For input 0, there are 3 choices. For input 1, there are 3 choices.
By the multiplication principle, the total number of functions is
$3 \\times 3 = 9$.

In the Counting and Pigeonhole world, you learned that
`Fintype.card_fun` gives the cardinality of a function type as an
exponential: $|\\beta^\\alpha| = |\\beta|^{|\\alpha|}$. Here that is
$|\\text{Fin 3}|^{|\\text{Fin 2}|} = 3^2 = 9$.

## Your task

Prove that `Fintype.card (Fin 2 → Fin 3) = 9`. Retrieve the
techniques from Level 2 of the Counting and Pigeonhole world.
"

/-- There are exactly 9 functions from `Fin 2` to `Fin 3`. -/
Statement : Fintype.card (Fin 2 → Fin 3) = 9 := by
  Hint "Start with `rw [Fintype.card_fun]` to express the function-type
  cardinality as an exponential."
  rw [Fintype.card_fun]
  Hint "Now the goal is `Fintype.card (Fin 3) ^ Fintype.card (Fin 2) = 9`.
  Rewrite both `Fintype.card (Fin _)` terms using `Fintype.card_fin`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `3 ^ 2 = 9`. Use `norm_num` to close it."
  norm_num

Conclusion
"
There are exactly 9 functions from `Fin 2` to `Fin 3`.

The proof followed three steps:
1. `Fintype.card_fun` gave: $|\\text{Fin 2} \\to \\text{Fin 3}| =
   |\\text{Fin 3}|^{|\\text{Fin 2}|}$.
2. `Fintype.card_fin` evaluated the base and exponent: $3^2$.
3. `norm_num` computed: $3^2 = 9$.

## Concretely: the 9 functions

Here they are, listed as $(f(0), f(1))$:

$(0,0), (0,1), (0,2), (1,0), (1,1), (1,2), (2,0), (2,1), (2,2)$

Each row in the table has 3 choices, and there are 2 rows, giving
$3^2 = 9$ functions total. This is the **multiplication principle**
in action.

**In plain language**: \"A function from a 2-element set to a
3-element set is determined by two independent choices from three
options, giving $3 \\times 3 = 9$ functions total.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
