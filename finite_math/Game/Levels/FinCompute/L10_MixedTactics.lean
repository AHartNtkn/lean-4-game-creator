import GameServer.Commands
import Mathlib

World "FinCompute"
Level 10

Title "Combining fin_cases with conjunctions"

Introduction
"
# `fin_cases` with Structured Goals

So far, you have used `fin_cases i <;> closer` where each case was
a single goal. Now let's combine `fin_cases` with `constructor` to
handle conjunctions --- goals that have two parts.

## The pattern

When each case of `fin_cases` produces a conjunction, you need to
split each case with `constructor` before closing. The combination
`fin_cases i <;> (constructor <;> norm_num)` does this:

1. `fin_cases i` --- split into one goal per element
2. `constructor` --- split each goal into two parts
3. `norm_num` --- close each part

This is a **nested semicolon** pattern: `<;>` applies `constructor`
to all goals from `fin_cases`, and then `<;>` again applies `norm_num`
to all goals from `constructor`.

## Your task

Prove that for every `i : Fin 3`:
- `i.val ^ 2 ≤ 4` (a power bound)
- `i.val + 1 ≤ 3` (a linear bound)

After `fin_cases i`, each case is a conjunction. Use
`fin_cases i <;> (constructor <;> norm_num)` to close all cases at once.
"

/-- Every element of `Fin 3` satisfies `i² ≤ 4` and `i + 1 ≤ 3`. -/
Statement : ∀ i : Fin 3, i.val ^ 2 ≤ 4 ∧ i.val + 1 ≤ 3 := by
  Hint "Start with `intro i` to introduce the variable."
  intro i
  Hint "Use `fin_cases i` to split into cases. Then handle each case."
  Hint (hidden := true) "After `fin_cases i`, each case is a conjunction.
  Try `fin_cases i <;> (constructor <;> norm_num)` to close all cases.
  Alternatively, handle each case individually:
  ```
  fin_cases i
  · constructor <;> norm_num
  · constructor <;> norm_num
  · constructor <;> norm_num
  ```"
  fin_cases i <;> (constructor <;> norm_num)

Conclusion
"
Each case was verified:
- `i = 0`: `0^2 = 0 ≤ 4` ✓ and `0 + 1 = 1 ≤ 3` ✓
- `i = 1`: `1^2 = 1 ≤ 4` ✓ and `1 + 1 = 2 ≤ 3` ✓
- `i = 2`: `2^2 = 4 ≤ 4` ✓ and `2 + 1 = 3 ≤ 3` ✓

Here `norm_num` was powerful enough to handle both the power and the
linear arithmetic. But the key skill is knowing that when `<;> omega`
fails (because of `^`), you can try `<;> norm_num` or `<;> (constructor <;> norm_num)`.

**Recap of closing tactics after `fin_cases`:**
- `omega`: linear arithmetic, inequalities
- `norm_num`: numeric evaluation, powers, products
- `decide`: decidable propositions (but may not be available)
- `constructor <;> closer`: when each case is a conjunction
- Manual handling: use `·` to address each case individually
"

DisabledTactic decide native_decide
