import GameServer.Commands
import Mathlib

World "CountingFunctions"
Level 5

Title "Boss: The multiplication principle"

Introduction
"
# Boss: Why $|\\text{Fin 2} \\to \\text{Fin 3}| = 3^2$

Time to tie it all together. In this world you have:
- counted all 9 functions `Fin 2 → Fin 3` (Level 1),
- counted the 6 injective ones (Level 2),
- shown that 0 are surjective (Level 3),
- counted the 8 functions `Fin 3 → Bool` (Level 4).

Every one of those results rested on the same foundation: the
**multiplication principle** for function types. The number of
functions from `α` to `β` is $|\\beta|^{|\\alpha|}$, because each of
the $|\\alpha|$ inputs independently chooses from $|\\beta|$ outputs.

## Your task

Prove the multiplication principle in a concrete, expanded form:
the number of functions `Fin 2 → Fin 3` equals the cardinality of
`Fin 3` **times** the cardinality of `Fin 3`.

This connects the abstract exponential formula back to the concrete
multiplication: $3^2 = 3 \\times 3$.

## The proof plan

1. Use `Fintype.card_fun` to rewrite as an exponential.
2. Use `Fintype.card_fin` to evaluate the pieces.
3. Close the arithmetic.
"

/-- The number of functions from `Fin 2` to `Fin 3` equals
`Fintype.card (Fin 3)` times itself. -/
Statement : Fintype.card (Fin 2 → Fin 3) =
    Fintype.card (Fin 3) * Fintype.card (Fin 3) := by
  Hint "Start with `rw [Fintype.card_fun]` to express the left-hand side
  as an exponential."
  rw [Fintype.card_fun]
  Hint "The goal is now
  `Fintype.card (Fin 3) ^ Fintype.card (Fin 2) =
   Fintype.card (Fin 3) * Fintype.card (Fin 3)`.

  Rewrite `Fintype.card (Fin 2)` to turn the exponent into a number."
  Hint (hidden := true) "Use `rw [Fintype.card_fin]` to replace
  `Fintype.card (Fin 2)` with `2`. The goal becomes
  `Fintype.card (Fin 3) ^ 2 = Fintype.card (Fin 3) * Fintype.card (Fin 3)`."
  rw [Fintype.card_fin 2]
  Hint "Now the goal is
  `Fintype.card (Fin 3) ^ 2 = Fintype.card (Fin 3) * Fintype.card (Fin 3)`.

  This is the identity $n^2 = n \\times n$. To close it, rewrite the
  remaining `Fintype.card (Fin 3)` and use arithmetic, or observe that
  `Nat.pow_two` or similar handles this."
  Hint (hidden := true) "Rewrite `Fintype.card (Fin 3)` to `3` using
  `rw [Fintype.card_fin]`, then `norm_num` closes `3 ^ 2 = 3 * 3`."
  rw [Fintype.card_fin]
  Hint (hidden := true) "The goal is `3 ^ 2 = 3 * 3`. Use `norm_num`."
  norm_num

Conclusion
"
Congratulations on completing the Counting Functions world!

You proved that the number of functions `Fin 2 → Fin 3` equals
$|\\text{Fin 3}| \\times |\\text{Fin 3}|$: three choices for the first
input, times three choices for the second input.

## The multiplication principle

The exponential rule $|\\beta^\\alpha| = |\\beta|^{|\\alpha|}$ is the
iterated multiplication principle: a function from `α` to `β` is
determined by $|\\alpha|$ independent choices, each from $|\\beta|$
options. The total is a product of $|\\alpha|$ copies of $|\\beta|$,
which is $|\\beta|^{|\\alpha|}$.

## What you learned in this world

| Concept | Level | Key item |
|---------|-------|----------|
| Counting all functions | L01 | `Fintype.card_fun` |
| Counting injective functions | L02 | `Fintype.card_embedding_eq` |
| No surjection from small to large | L03 | `Fintype.card_le_of_surjective` |
| Functions to Bool as subsets | L04 | `Fintype.card_bool` |
| The multiplication principle | L05 | Integration |

## Transfer moment

In paper mathematics, you would write:

> *There are $3^2 = 9$ functions from a 2-element set to a 3-element set.
> Of these, $3 \\cdot 2 = 6$ are injective and none are surjective.
> More generally, $|\\beta^\\alpha| = |\\beta|^{|\\alpha|}$ by the
> multiplication principle: each of the $|\\alpha|$ inputs independently
> chooses from $|\\beta|$ outputs.*

The Lean proof mechanizes each step: `Fintype.card_fun` states the
exponential rule, `Fintype.card_fin` evaluates the specific sizes,
and arithmetic closes the computation. The mathematical insight is
identical.
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
