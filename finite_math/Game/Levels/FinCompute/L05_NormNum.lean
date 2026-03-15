import GameServer.Commands
import Mathlib

World "FinCompute"
Level 5

Title "Introducing norm_num"

Introduction
"
# The `norm_num` Tactic

The `norm_num` tactic is specialized for **numeric computations**. It can
evaluate arithmetic expressions, verify equalities and inequalities
involving concrete numbers, and simplify numeric goals.

## How `norm_num` differs from `omega`

- `omega` works with **linear** arithmetic over natural numbers and
  integers. It handles `+`, `-`, `*` (by a constant), `<`, `≤`, `=`.
- `norm_num` handles **general** numeric computation, including
  multiplication, division, powers (`^`), and evaluation of specific
  numeric functions.

For simple arithmetic, both work. But `omega` **cannot** handle powers
like `2 ^ 3` or `3 ^ 2`. When you see `^` in a goal, reach for `norm_num`.

## Your task

Prove that `(3 : Fin 10).val ^ 2 = 9`.

Here, `(3 : Fin 10).val = 3`, so the goal reduces to `3 ^ 2 = 9`. The
`omega` tactic cannot handle this (try it and see!), but `norm_num`
evaluates it easily.
"

/-- The square of `3` in `Fin 10` (as a natural number) equals `9`. -/
Statement : (3 : Fin 10).val ^ 2 = 9 := by
  Hint "This involves a power (`^`), so `omega` will not work. Try `norm_num`."
  Hint (hidden := true) "`norm_num` evaluates `3 ^ 2` to `9` and verifies
  the equality. It handles all standard numeric operations including powers."
  norm_num

/-- `norm_num` evaluates numeric expressions and closes goals involving
concrete arithmetic. It handles addition, multiplication, powers, division,
and other standard numeric operations.

**Example**: `norm_num` can verify `2 ^ 10 = 1024` or `17 * 23 = 391`.

**When to use**: When your goal involves concrete numeric computation,
especially powers (`^`), products, or other non-linear expressions that
`omega` cannot handle.

**Compared to `omega`**: `omega` handles linear arithmetic with variables
(e.g., `x + 3 ≤ y + 5`). `norm_num` handles concrete numeric evaluation
(e.g., `2 ^ 8 = 256`). They complement each other. -/
TacticDoc norm_num

Conclusion
"
`norm_num` evaluated the expression step by step:
1. `(3 : Fin 10).val = 3` (the underlying natural number)
2. `3 ^ 2 = 9` (arithmetic)
3. `9 = 9` ✓

Notice that `omega` would have failed here. Try replacing `norm_num` with
`omega` to see: `omega` reports that it cannot handle the `^` operator.
This is the key difference:

- **`omega`**: linear arithmetic (`+`, `-`, `*` by constants, inequalities)
- **`norm_num`**: general numeric evaluation (products, **powers**, factorials)

In later worlds, `norm_num` will be essential for computing with
factorials, binomial coefficients, and cardinalities. For now, think
of it as the \"numeric calculator\" tactic.

**The tactic trio for numeric goals:**
| Goal type | Best tactic |
|-----------|-------------|
| Linear arithmetic with variables | `omega` |
| Powers, products of concrete numbers | `norm_num` |
| Decidable propositions on finite types | `decide` |
"

NewTactic norm_num
DisabledTactic decide omega native_decide
