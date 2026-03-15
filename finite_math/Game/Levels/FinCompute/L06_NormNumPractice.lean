import GameServer.Commands
import Mathlib

World "FinCompute"
Level 6

Title "norm_num practice: powers on Fin"

Introduction
"
# Combining `fin_cases` and `norm_num`

Now let's use `fin_cases` and `norm_num` together. When a universal statement
about `Fin n` involves powers or non-linear arithmetic, the pattern is:

1. `intro i` to introduce the variable
2. `fin_cases i` to split into cases
3. `norm_num` to evaluate each case

Since `omega` cannot handle `^`, we need `norm_num` as the closer here.

## Your task

Prove that every element `i` of `Fin 4` satisfies `i.val ^ 2 + 1 ≤ 10`.

The values are:
- `i = 0`: `0^2 + 1 = 1 ≤ 10` ✓
- `i = 1`: `1^2 + 1 = 2 ≤ 10` ✓
- `i = 2`: `2^2 + 1 = 5 ≤ 10` ✓
- `i = 3`: `3^2 + 1 = 10 ≤ 10` ✓

Use `fin_cases i <;> norm_num`.
"

/-- The function `i² + 1` stays at most 10 on `Fin 4`. -/
Statement : ∀ i : Fin 4, i.val ^ 2 + 1 ≤ 10 := by
  Hint "Start with `intro i` to introduce the variable."
  intro i
  Hint "Use `fin_cases i <;> norm_num` to check each case."
  Hint (hidden := true) "Since the goal involves `^`, `omega` would fail.
  `norm_num` evaluates the power and checks the inequality for each concrete value."
  fin_cases i <;> norm_num

Conclusion
"
You just used the **exhaustive verification** pattern with a new closer:
`norm_num` instead of `omega`. The structure is the same ---

```
intro i; fin_cases i <;> closer
```

--- but the closer must match the arithmetic. When the goal involves:
- `+`, `-`, `<`, `≤` with variables: `omega`
- `^`, `*`, concrete numeric evaluation: `norm_num`

This `fin_cases <;> norm_num` combination will appear frequently when
verifying properties of polynomial or power expressions on finite types.
"

DisabledTactic decide omega native_decide
