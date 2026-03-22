import Game.Metadata

World "PascalsTriangle"
Level 4

Title "Not in the Antidiagonal"

Introduction "
# What's NOT in an Antidiagonal

The pair $(2, 4)$ is NOT in `antidiagonal 5`, because $2 + 4 = 6 \\neq 5$.
Only pairs whose coordinates sum to **exactly** $n$ qualify.

To prove non-membership, unfold the definition with
`Finset.mem_antidiagonal`, which produces the goal `¬(2 + 4 = 5)`.
Then `omega` handles the arithmetic.

**Your task**: Prove $(2, 4) \\notin \\text{antidiagonal}(5)$.
"

/-- (2, 4) is not in the 5th antidiagonal. -/
Statement : (2, 4) ∉ Finset.antidiagonal 5 := by
  Hint "Use `rw [Finset.mem_antidiagonal]` to convert the membership
  condition to arithmetic. Since `∉` is `¬(... ∈ ...)`, the rewrite
  targets the inner membership, giving `¬(2 + 4 = 5)`.
  Then `omega` handles the contradiction."
  Hint (hidden := true) "Try `rw [Finset.mem_antidiagonal]` first.
  Then `omega` closes the negation."
  rw [Finset.mem_antidiagonal]
  Hint "The goal is `¬((2, 4).1 + (2, 4).2 = 5)`, which reduces to
  `¬(2 + 4 = 5)`. The `omega` tactic can close this: $6 \\neq 5$."
  Hint (hidden := true) "Try `omega`."
  omega

Conclusion "
$(2, 4) \\notin \\text{antidiagonal}(5)$ because $2 + 4 = 6 \\neq 5$.

The pair $(2, 4)$ belongs to `antidiagonal 6` instead.

**Pattern**: To prove `p ∉ antidiagonal n`:
1. `rw [Finset.mem_antidiagonal]` — convert to arithmetic
2. `omega` — the contradiction $i + j \\neq n$

To prove `p ∈ antidiagonal n`:
1. `rw [Finset.mem_antidiagonal]` — convert to arithmetic
2. `omega` — the identity $i + j = n$

Both directions use the same tool: `mem_antidiagonal` reduces
membership to a simple arithmetic question.
"

TheoremTab "Finset"

DisabledTactic trivial «decide» native_decide simp aesop simp_all norm_num rfl tauto linarith nlinarith
DisabledTheorem Nat.add_choose_eq
