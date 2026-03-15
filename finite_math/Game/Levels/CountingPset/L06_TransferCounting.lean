import GameServer.Commands
import Mathlib

World "CountingPset"
Level 6

Title "Transfer: The exponential formula"

Introduction
"
# Transfer: Why `Fin 4 → Fin 3` has $3^4 = 81$ elements

Compute the cardinality of `Fin 4 → Fin 3`. The answer is
$|\\text{Fin 3}|^{|\\text{Fin 4}|} = 3^4 = 81$.

The Lean proof is a direct application of `Fintype.card_fun` and
`Fintype.card_fin`. The real lesson is in the conclusion, where
you will see why the formula works.
"

/-- There are exactly 81 functions from `Fin 4` to `Fin 3`. -/
Statement : Fintype.card (Fin 4 → Fin 3) = 81 := by
  Hint (hidden := true) "Use `rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]`,
  then close with `norm_num`."
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
  norm_num

Conclusion
"
There are exactly 81 functions from `Fin 4` to `Fin 3`.

## The paper explanation

> *A function $f : \\{0, 1, 2, 3\\} \\to \\{0, 1, 2\\}$ is determined
> by four independent choices: $f(0)$, $f(1)$, $f(2)$, and $f(3)$.
> Each choice has 3 options. By the multiplication principle, the
> total number of functions is $3 \\times 3 \\times 3 \\times 3 = 3^4 = 81$.*

The exponential formula $|\\beta^\\alpha| = |\\beta|^{|\\alpha|}$ captures
this: the codomain size is the **base** (each input chooses from
$|\\beta|$ options) and the domain size is the **exponent** (there are
$|\\alpha|$ independent choices).

## Comparing previous computations

| Function type | Count | Formula |
|---------------|-------|---------|
| `Fin 2 → Fin 3` | 9 | $3^2$ |
| `Fin 3 → Bool` | 8 | $2^3$ |
| `Fin 4 → Fin 3` | 81 | $3^4$ |

The same principle, different numbers.

**Transfer check**: You can now explain in ordinary language why the
number of functions from an $m$-element set to an $n$-element set
is $n^m$.
"

DisabledTactic trivial decide native_decide simp aesop simp_all
