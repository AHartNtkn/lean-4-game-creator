import GameServer.Commands
import Mathlib

World "CountingPigeonhole"
Level 2

Title "Cardinality of function types"

Introduction
"
# Function types have computable cardinality

Perhaps surprisingly, the type of **all functions** from a finite type to
a finite type is itself finite, and its cardinality follows the exponential
rule:
```
Fintype.card_fun : Fintype.card (α → β) = Fintype.card β ^ Fintype.card α
```

Think about it: a function `f : Fin 2 → Fin 3` must assign each of the
2 inputs a value from 3 choices. That gives $3 \\times 3 = 3^2 = 9$
possible functions.

## Your task

Prove that `Fintype.card (Fin 2 → Fin 3) = 9`.

This requires:
1. `Fintype.card_fun` to express the cardinality as an exponent.
2. `Fintype.card_fin` to evaluate the base and exponent.
3. A numeric step to show $3^2 = 9$.
"

/-- There are exactly 9 functions from `Fin 2` to `Fin 3`. -/
Statement : Fintype.card (Fin 2 → Fin 3) = 9 := by
  Hint "Use `rw [Fintype.card_fun]` to rewrite the function-type cardinality
  as `Fintype.card (Fin 3) ^ Fintype.card (Fin 2)`.

  Note the order: the **codomain** cardinality is the base, and the
  **domain** cardinality is the exponent."
  rw [Fintype.card_fun]
  Hint "Now rewrite the `Fintype.card (Fin _)` terms using `Fintype.card_fin`.
  The goal will become `3 ^ 2 = 9`."
  rw [Fintype.card_fin, Fintype.card_fin]
  Hint (hidden := true) "The goal is `3 ^ 2 = 9`. Use `norm_num` to close
  this arithmetic goal."
  norm_num

Conclusion
"
The exponential counting principle:

1. `Fintype.card_fun` gave: `|\\text{Fin 2} \\to \\text{Fin 3}| =
   |\\text{Fin 3}|^{|\\text{Fin 2}|}`.
2. `Fintype.card_fin` evaluated: $3^2$.
3. `norm_num` computed: $3^2 = 9$.

## The multiplication principle for functions

Why $3^2$? Each of the 2 inputs independently chooses from 3 outputs.
By the multiplication principle, the total count is $3 \\times 3 = 3^2$.

More generally, $|\\beta^\\alpha| = |\\beta|^{|\\alpha|}$. This is
the exponential rule for counting functions, and it is why function
types are sometimes written with exponential notation.

**In plain language**: \"There are $3^2 = 9$ ways to assign one of three
values to each of two slots.\"
"

/-- `Fintype.card_fun` states that the cardinality of a function type is
an exponential:
```
Fintype.card_fun : Fintype.card (α → β) = Fintype.card β ^ Fintype.card α
```

Note the order: **codomain** to the power of **domain**.

**When to use**: When computing how many functions exist between two finite
types. -/
TheoremDoc Fintype.card_fun as "Fintype.card_fun" in "Fintype"

NewTheorem Fintype.card_fun
TheoremTab "Fintype"
DisabledTactic trivial decide native_decide aesop simp_all
