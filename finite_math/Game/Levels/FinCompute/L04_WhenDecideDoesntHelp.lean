import GameServer.Commands
import Mathlib

World "FinCompute"
Level 4

Title "When decide doesn't help"

Introduction
"
# `fin_cases` When You Need Per-Case Reasoning

`decide` is convenient, but it treats the entire goal as a single
computation. Sometimes you need **control over individual cases** ---
for example, when each case requires a different lemma or rewriting
step.

## `decide` vs `fin_cases`

- **`decide`**: One tactic, no follow-up. Best for fully concrete
  propositions on small finite types.
- **`fin_cases`**: Splits into one goal per element. You choose what
  to do in each case. Essential when per-case reasoning varies.

## Your task

Prove that for every `i : Fin 4`, `i.val + 1 ≤ 4` and `2 * i.val < 8`.

This is a conjunction of two linear inequalities. After `fin_cases i`,
you get four cases, each a concrete arithmetic check. The semicolon
combinator `<;> omega` handles all of them.

Notice that `decide` is **disabled** for this level. The point is to
build your `fin_cases` fluency and see how `fin_cases` gives you
control that `decide` does not.

**Rule of thumb**:
- Try `decide` first for fully concrete propositions.
- Use `fin_cases` when you need manual reasoning in some cases,
  or when `decide` is too slow.
- Use `i.isLt` + `omega` when the property holds for all `Fin n`
  (not just a specific `n`).
"

/-- Every element of `Fin 4` satisfies both `i + 1 ≤ 4` and `2i < 8`. -/
Statement : ∀ i : Fin 4, i.val + 1 ≤ 4 ∧ 2 * i.val < 8 := by
  Hint "Start with `intro i` to introduce the variable."
  intro i
  Hint "Use `fin_cases i` to split into four cases."
  Hint (hidden := true) "After `fin_cases i`, use `<;> omega` to close all cases.
  The `omega` tactic handles the conjunction and the linear arithmetic
  in each concrete case."
  fin_cases i <;> omega

Conclusion
"
Each case was checked individually:
- `i = 0`: `0 + 1 ≤ 4` and `2 * 0 < 8` ✓
- `i = 1`: `1 + 1 ≤ 4` and `2 * 1 < 8` ✓
- `i = 2`: `2 + 1 ≤ 4` and `2 * 2 < 8` ✓
- `i = 3`: `3 + 1 ≤ 4` and `2 * 3 < 8` ✓

With `decide` disabled, you had to use `fin_cases`. In practice,
both tactics would work here. The real difference emerges when:

1. **`decide` times out**: For `Fin 20` or larger, the brute-force
   computation may be too slow. `fin_cases` + a targeted closer still
   works.

2. **Per-case reasoning varies**: If case `i = 0` needs `rw` and
   case `i = 1` needs `apply`, `fin_cases` lets you handle each
   separately. `decide` cannot do this.

3. **Insight**: `fin_cases` tells you *why* the proof works (each case
   checked). `decide` just says \"it's true.\" For learning, `fin_cases`
   gives you more.

The three strategies for `Fin n` proofs:
| Strategy | Scope | Control |
|----------|-------|---------|
| `decide` | small concrete `n`, fully decidable goals | none (black box) |
| `fin_cases` + closer | small concrete `n`, any per-case goal | per-case |
| `i.isLt` + `omega` | any `n`, goals following from the bound | algebraic |
"

DisabledTactic decide native_decide
