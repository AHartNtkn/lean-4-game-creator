import GameServer.Commands
import Mathlib

World "CountingFunctions"
Level 4

Title "Fin 3 → Bool has 8 elements"

Introduction
"
# Functions to Bool: Exponential Counting

Consider the type `Fin 3 → Bool`. A function of this type assigns
to each of 3 inputs one of 2 boolean values (`true` or `false`).

How many such functions are there? By the exponential rule:
$|\\text{Bool}|^{|\\text{Fin 3}|} = 2^3 = 8$.

Notice the switch: in Level 1 you counted `Fin 2 → Fin 3` and got
$3^2 = 9$. Now you count `Fin 3 → Bool` and get $2^3 = 8$. The
base and exponent swap roles because **the base is the codomain** and
**the exponent is the domain**.

## A concrete view

A function `Fin 3 → Bool` is essentially a **bit string of length 3**.
The 8 such strings are:

$\\text{FFF}, \\text{FFT}, \\text{FTF}, \\text{FTT},
 \\text{TFF}, \\text{TFT}, \\text{TTF}, \\text{TTT}$

Each bit string corresponds to a **subset of Fin 3** (which elements
are \"in\" the subset). There are $2^3 = 8$ subsets of a 3-element set
--- exactly the power set.

## Your task

Prove that `Fintype.card (Fin 3 → Bool) = 8`.

You will use `Fintype.card_fun`, `Fintype.card_fin`, and
`Fintype.card_bool`.
"

/-- There are exactly 8 functions from `Fin 3` to `Bool`. -/
Statement : Fintype.card (Fin 3 → Bool) = 8 := by
  Hint "Start with `rw [Fintype.card_fun]` to express the function-type
  cardinality as an exponential."
  rw [Fintype.card_fun]
  Hint "Now rewrite `Fintype.card (Fin 3)` and `Fintype.card Bool`
  using their respective lemmas."
  Hint (hidden := true) "Use `rw [Fintype.card_fin, Fintype.card_bool]`."
  rw [Fintype.card_fin, Fintype.card_bool]
  Hint (hidden := true) "The goal is `2 ^ 3 = 8`. Use `norm_num` to close it."
  norm_num

Conclusion
"
There are exactly 8 functions from `Fin 3` to `Bool`, corresponding
to the $2^3 = 8$ subsets of a 3-element set.

The proof was:
1. `Fintype.card_fun` gave: $|\\text{Fin 3} \\to \\text{Bool}| =
   |\\text{Bool}|^{|\\text{Fin 3}|}$.
2. `Fintype.card_fin` and `Fintype.card_bool` evaluated: $2^3$.
3. `norm_num` computed: $2^3 = 8$.

## Functions to Bool as subsets

This connection between `α → Bool` and subsets of `α` is fundamental:
- Each function `f : α → Bool` defines the subset
  $\\{x \\in \\alpha \\mid f(x) = \\text{true}\\}$.
- Each subset $S \\subseteq \\alpha$ defines the characteristic function
  $\\chi_S(x) = \\text{true iff } x \\in S$.

The number of subsets of an $n$-element set is $2^n$. This is why
the power set is denoted $\\mathcal P(\\alpha)$ or $2^\\alpha$.

## Comparing the two exponentials

| Function type | Count | Formula |
|---------------|-------|---------|
| `Fin 2 → Fin 3` | 9 | $3^2$ (Level 1) |
| `Fin 3 → Bool` | 8 | $2^3$ (this level) |

The codomain size is always the **base** of the exponential. The
domain size is always the **exponent**.

**In plain language**: \"There are $2^3 = 8$ binary strings of length 3,
or equivalently, $8$ subsets of a 3-element set.\"
"

TheoremTab "Fintype"
DisabledTactic trivial decide native_decide simp aesop simp_all
