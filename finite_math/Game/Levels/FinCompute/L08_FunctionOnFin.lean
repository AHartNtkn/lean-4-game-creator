import GameServer.Commands
import Mathlib

World "FinCompute"
Level 8

Title "Computing a sum over Fin by hand"

Introduction
"
# Computing with Functions on `Fin n`

A powerful use of `fin_cases` is verifying properties of specific
functions defined on `Fin n`. Instead of proving a proposition about all
elements, you **check what the function does on each input**.

## Functions on `Fin n` by cases

Consider a function `f : Fin 3 → ℕ` defined as `f i = i.val ^ 2 + 1`.

To verify that `f` sends every element to a value below `10`, we:
1. `intro i` to pick an arbitrary input
2. `fin_cases i` to enumerate all three inputs
3. Verify the output for each: `f 0 = 1`, `f 1 = 2`, `f 2 = 5` --- all `< 10`

This is the **function verification by exhaustion** pattern. It is the
computational sibling of the universal-property proofs from earlier levels,
but the framing is different: we think of the proof as \"checking the
function's output table.\"

## Your task

Define `f : Fin 3 → ℕ` by `f i = i.val ^ 2 + 1`. Prove that the
sum of `f`'s outputs equals `8`.

More precisely, prove:

`(0 : Fin 3).val ^ 2 + 1 + ((1 : Fin 3).val ^ 2 + 1) + ((2 : Fin 3).val ^ 2 + 1) = 8`

This just evaluates `f(0) + f(1) + f(2) = 1 + 2 + 5 = 8`.

The `norm_num` tactic can evaluate this directly.
"

/-- The sum of `i² + 1` over all `i` in `Fin 3` equals 8. -/
Statement : (0 : Fin 3).val ^ 2 + 1 + ((1 : Fin 3).val ^ 2 + 1) + ((2 : Fin 3).val ^ 2 + 1) = 8 := by
  Hint "This is a concrete numeric computation. Try `norm_num`."
  Hint (hidden := true) "`norm_num` will evaluate `0^2 + 1 = 1`, `1^2 + 1 = 2`,
  `2^2 + 1 = 5`, and then `1 + 2 + 5 = 8`."
  norm_num

Conclusion
"
You just verified a function's output table:
- `f(0) = 0^2 + 1 = 1`
- `f(1) = 1^2 + 1 = 2`
- `f(2) = 2^2 + 1 = 5`
- Sum: `1 + 2 + 5 = 8` ✓

This is the pattern for **computing with functions on `Fin n`**:
enumerate the inputs, compute the outputs, verify the property.

In later worlds, you will learn `Finset.sum` and `Finset.prod`, which
let you express sums over all elements of a finite type directly in
Lean notation. But the underlying proof idea is the same: the sum is
computed by checking every input.

**Transfer to paper proofs**: This is exactly what a mathematician
means by \"we compute the sum by evaluating $f$ at each element of
the domain.\" The `norm_num` tactic automates the arithmetic, while
on paper you would show the computation table explicitly.
"

DisabledTactic decide native_decide
